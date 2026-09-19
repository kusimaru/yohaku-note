import { PAGE_WIDTH as W, MAX_HEIGHT, newPage, newTextBlock, inkWidth, hitStroke, erasePart, splitByPolygon, pointInPolygon, validateBackup, upgradeNotebook, ensureStructure, notebookOf, sectionOf, sectionsIn, pagesIn, addNotebook, addSection, renameNotebook, renameSection, setSectionColor, setNotebookColor, movePage, moveSection, moveNotebook, deletePage, deleteSection, deleteNotebook, restoreTrash, purgeTrash, emptyTrash, mergeNotebook, SECTION_COLORS } from './model.mjs';
import { openStore, loadNotebook, saveNotebook, migrateNotebook } from './storage.mjs';
import { domToRuns, runsToDom, toHex } from './richtext.mjs';
import { pageToSvg } from './svgexport.mjs';
import { createSyncEngine, createFirebaseTransport, createFakeTransport, describeAuthError } from './sync.mjs';
import { normalizeRuns, runsToText, blockRuns, DEFAULT_TEXT_COLOR, MIN_FONT, MAX_FONT, MAX_LAYERS, ensureLayers, activeLayerOf, addLayer, removeLayer, updateLayer, moveLayer } from './model.mjs';
const off=document.createElement('canvas'),octx=off.getContext('2d');
const lastRuns=new WeakMap();
const $=id=>document.getElementById(id);
const SVG_NS='http://www.w3.org/2000/svg';
function icon(name,cls='') {
 const svg=document.createElementNS(SVG_NS,'svg');svg.setAttribute('class','icon'+(cls?' '+cls:''));svg.setAttribute('aria-hidden','true');
 const use=document.createElementNS(SVG_NS,'use');use.setAttribute('href','#i-'+name);svg.append(use);return svg;
}
const sheet=$('sheet'),canvas=$('canvas'),ctx=canvas.getContext('2d'),blocksLayer=$('blocks'),paper=$('paper'),selectionEl=$('selection'),marqueeEl=$('marquee'),lassoEl=$('lasso'),eraserCursor=$('eraser-cursor');
let db,doc,ready=false,tool='text',eraserMode='part',eraserSize=8,color='#243c3a',width=4,gesture=null,scale=1,activeBlock=null;
let selection={strokes:new Set(),blocks:new Set()},selectionLasso=null,arrowBatch=-1e9,selectMode='rect',dragging=null,view='pages',menuTarget=null,formMode=null,clearArmed=-1e9;
const collapsedNotebooks=new Set();let selectedSectionId=null,lastShownSectionId=null;
let pageSort='manual';try{pageSort=['manual','updated','name'].includes(localStorage.getItem('yohaku-page-sort'))?localStorage.getItem('yohaku-page-sort'):'manual';}catch{}
let dirty=false,saving=false,revision=0,saveFailed=false,lastInkEnd=-1e9,editing=null,lastPaperWidth=0;
const histories=new Map();
const page=()=>doc.pages.find(p=>p.id===doc.activeId);
const pageById=id=>doc.pages.find(p=>p.id===id);
const historyFor=id=>{if(!histories.has(id))histories.set(id,{undo:[],redo:[]});return histories.get(id);};
const clamp=(v,lo,hi)=>Math.max(lo,Math.min(hi,v));
const snapshot=p=>{ensureLayers(p);return {strokes:p.strokes.slice(),blocks:p.blocks.slice(),height:p.height,layers:p.layers.slice(),activeLayer:p.activeLayer};};
function restore(p,s){p.strokes=s.strokes;p.blocks=s.blocks;p.height=s.height;if(s.layers){p.layers=s.layers;p.activeLayer=s.activeLayer;}}
function message(text,retry=false) {
 $('message').replaceChildren(document.createTextNode(text));$('message').hidden=false;
 if(retry){const button=document.createElement('button');button.textContent='保存を再試行';button.onclick=()=>{saveFailed=false;save();};$('message').append(' ',button);}
}
function setStatus(text,error=false){$('save-status').replaceChildren(...(text==='保存済み'?[icon('check'),' ']:[]),text);$('save-status').classList.toggle('error',error);}
let saveTimer=0;
// Which items the next save must write. Pages/trash entries that appear or disappear are
// detected by comparing ids with the last successful save; everything else is marked here.
const dirtyPages=new Set(),dirtyTrash=new Set();let dirtyAll=false,dropLegacy=false,lastSaved={pages:new Set(),trash:new Set()};
// Pages changed indirectly (moved to another category, category renamed) must be saved and uploaded too.
function touchPages(ids){for(const id of ids){dirtyPages.add(id);const pg=doc.pages.find(x=>x.id===id);if(pg)pg.updatedAt=Date.now();if(syncEngine&&!applyingRemote)syncEngine.markPage(id);}}
function changed(p=page()) {
 p.updatedAt=Date.now();revision++;dirty=true;dirtyPages.add(p.id);
 setStatus('保存中…');clearTimeout(saveTimer);saveTimer=setTimeout(save,300);
 if(syncEngine&&!applyingRemote){syncEngine.markPage(p.id);syncObserve();}
}
async function save() {
 if(saving||!db||!dirty)return;
 saving=true;
 try {
  while(dirty) {
   const version=revision;
   const set={pages:new Set(dirtyPages),trash:new Set(dirtyTrash)},all=dirtyAll,legacy=dropLegacy;
   dirtyPages.clear();dirtyTrash.clear();dirtyAll=false;dropLegacy=false;
   for(const pg of doc.pages)if(!lastSaved.pages.has(pg.id))set.pages.add(pg.id);
   for(const t of doc.trash||[])if(!lastSaved.trash.has(t.id))set.trash.add(t.id);
   try{await saveNotebook(db,doc,all?null:set,legacy);}
   catch(e){for(const id of set.pages)dirtyPages.add(id);for(const id of set.trash)dirtyTrash.add(id);if(all)dirtyAll=true;if(legacy)dropLegacy=true;throw e;}
   lastSaved={pages:new Set(doc.pages.map(pg=>pg.id)),trash:new Set((doc.trash||[]).map(t=>t.id))};
   if(version===revision)dirty=false;
  }
  setStatus('保存済み');
  if(saveFailed){$('message').hidden=true;saveFailed=false;}
 } catch(error) {
  saveFailed=true;setStatus('未保存 — バックアップを推奨',true);
  message('自動保存できませんでした。現在のメモは画面に残っています。「バックアップを書き出す」で保存してから、保存を再試行してください。',true);
  console.warn('保存に失敗:',error.name);
 } finally {saving=false;}
}
function commit(before,p=page()) {
 const h=historyFor(p.id);h.undo.push(before);if(h.undo.length>40)h.undo.shift();h.redo=[];
 changed(p);syncHistory();
}
function syncHistory() {
 const h=historyFor(doc.activeId);$('undo').disabled=!ready||h.undo.length===0;$('redo').disabled=!ready||h.redo.length===0;
}
// ---- navigation: notebooks › sections | pages ----
const el=(tag,cls,text)=>{const e=document.createElement(tag);if(cls)e.className=cls;if(text!==undefined)e.textContent=text;return e;};
function currentSection() {
 ensureStructure(doc);
 if(selectedSectionId&&sectionOf(doc,selectedSectionId))return sectionOf(doc,selectedSectionId);
 return sectionOf(doc,page().sectionId)||doc.sections[0];
}
function openPage(id) {
 if(id===doc.activeId){selectedSectionId=null;renderPages();return;}
 finish();doc.activeId=id;selectedSectionId=null;revision++;dirty=true;showPage();save();
}
function selectSection(id) {
 const first=pagesIn(doc,id)[0];
 if(first){openPage(first.id);}else{selectedSectionId=id;renderPages();}
}
function renderPages() {
 $('pages').replaceChildren();closeMenu();ensureStructure(doc);
 $('trash-count').textContent=(doc.trash||[]).length;$('trash-toggle').classList.toggle('active',view==='trash');$('trash-toggle').setAttribute('aria-pressed',String(view==='trash'));
 document.querySelector('.nav-cols').classList.toggle('trash',view==='trash');
 if(view==='trash'){renderTrash();return;}
 renderNotebooks();renderPageList();renderSectionSelect();
}
function renderNotebooks() {
 const box=$('notebooks');box.replaceChildren();const cur=currentSection();
 // when the open section changes (page opened, section picked, page moved), reveal its notebook; otherwise respect the user's fold
 if(cur.id!==lastShownSectionId){lastShownSectionId=cur.id;collapsedNotebooks.delete(cur.notebookId);}
 for(const nb of doc.notebooks){
  const secs=sectionsIn(doc,nb.id),open=!collapsedNotebooks.has(nb.id);
  const wrap=el('div','notebook'+(open?'':' collapsed'));wrap.dataset.notebookId=nb.id;
  const head=el('div','notebook-head');
  const btn=el('button','notebook-button');btn.type='button';btn.draggable=true;btn.dataset.notebookId=nb.id;btn.setAttribute('aria-expanded',String(open));btn.title='クリックで開閉 / ドラッグで並べ替え';
  const nbIcon=el('span','nb-icon');nbIcon.style.setProperty('--sec',nb.color);
  btn.append(icon('chevron-down','chev'),nbIcon,el('span','nb-name',nb.name));
  btn.onclick=()=>{if(collapsedNotebooks.has(nb.id))collapsedNotebooks.delete(nb.id);else collapsedNotebooks.add(nb.id);renderPages();};
  head.append(btn,menuButton({type:'notebook',id:nb.id,label:nb.name}));wrap.append(head);
  if(open){
   const list=el('div','sections');
   for(const sec of secs){
    const row=el('div','section-row');
    const tab=el('button','section-tab'+(sec.id===cur.id?' active':''));tab.type='button';tab.draggable=true;tab.dataset.sectionId=sec.id;tab.style.setProperty('--sec',sec.color);
    tab.append(icon('section','sec-icon'),el('span','sec-name',sec.name));tab.title='クリックで開く / ドラッグで並べ替え・移動';
    tab.onclick=()=>selectSection(sec.id);
    row.append(tab,menuButton({type:'section',id:sec.id,label:sec.name}));list.append(row);
   }
   const add=el('button','add-section-link');add.type='button';add.dataset.notebookId=nb.id;add.append(icon('plus'),'新しいセクション');
   add.onclick=()=>showForm({kind:'new-section',notebookId:nb.id},'新しいセクション（'+nb.name+'）','','作成');
   list.append(add);wrap.append(list);
  }
  box.append(wrap);
 }
}
function sortedPages(sectionId) {
 const list=pagesIn(doc,sectionId);
 if(pageSort==='updated')return [...list].sort((a,b)=>(b.updatedAt||0)-(a.updatedAt||0));
 if(pageSort==='name')return [...list].sort((a,b)=>(a.title||'').localeCompare(b.title||'','ja'));
 return list;
}
function renderPageList() {
 const cur=currentSection(),head=$('current-section');head.replaceChildren();head.style.setProperty('--sec',cur.color);
 const nb=notebookOf(doc,cur.notebookId);head.append(icon('section','sec-icon'),el('span','',(nb?nb.name+' › ':'')+cur.name));
 const list=sortedPages(cur.id),box=$('pages');
 for(const pg of list){
  const button=el('button','page-button'+(pg.id===doc.activeId?' active':''));button.type='button';button.dataset.pageId=pg.id;button.draggable=true;button.setAttribute('aria-current',pg.id===doc.activeId?'page':'false');
  const name=el('span'),label=el('span','',pg.title||'名称未設定');name.append(icon('page'),label);button.append(name);
  const sub=el('small','',new Date(pg.updatedAt).toLocaleDateString('ja-JP'));button.append(sub);
  button.onclick=()=>openPage(pg.id);
  const item=el('div','page-item');item.append(button,menuButton({type:'page',id:pg.id,label:pg.title||'名称未設定'}));box.append(item);
 }
 if(!list.length)box.append(el('div','pages-empty','このセクションにはまだページがありません。「ページの追加」で作れます。'));
 $('page-count').textContent=list.length;
 const labels={manual:'手動（ドラッグ順）',updated:'更新日が新しい順',name:'名前順'};
 $('sort-pages').title='並べ替え：'+labels[pageSort]+'（押すと切り替え）';$('sort-pages').classList.toggle('active',pageSort!=='manual');
}
$('sort-pages').onclick=()=>{pageSort=pageSort==='manual'?'updated':pageSort==='updated'?'name':'manual';try{localStorage.setItem('yohaku-page-sort',pageSort);}catch{}renderPageList();
 const labels={manual:'手動（ドラッグ順）',updated:'更新日が新しい順',name:'名前順'};message('ページの並べ替え：'+labels[pageSort]);};
function renderSectionSelect() {
 const sel=$('page-section');sel.replaceChildren();const cur=page().sectionId;
 for(const nb of doc.notebooks){
  const g=document.createElement('optgroup');g.label=nb.name;
  for(const sec of sectionsIn(doc,nb.id)){const o=document.createElement('option');o.value=sec.id;o.textContent=sec.name;if(sec.id===cur)o.selected=true;g.append(o);}
  sel.append(g);
 }
}
$('page-section').onchange=e=>{
 const p=page();if(!movePage(doc,p.id,e.target.value))return;
 touchPages([p.id]);changed();breadcrumb();renderPages();
};
// ---- item menu (rename / colour / delete) ----
function menuButton(target) {
 const b=document.createElement('button');b.type='button';b.className='item-menu-button';b.append(icon('more'));b.draggable=false;
 const kind={page:'ページ',section:'セクション',notebook:'ノートブック'}[target.type];
 b.setAttribute('aria-label',kind+'「'+target.label+'」のメニュー');b.setAttribute('aria-haspopup','menu');
 b.onclick=e=>{e.stopPropagation();openMenu(target,b.getBoundingClientRect(),b.parentElement);};
 return b;
}
function openMenu(target,rect,holder) {
 closeMenu();menuTarget={...target,holder};holder?.classList.add('menu-open');
 const menu=$('item-menu');menu.hidden=false;
 const colors=$('menu-colors');colors.replaceChildren();
 if(target.type!=='page'){
  const current=target.type==='section'?sectionOf(doc,target.id)?.color:notebookOf(doc,target.id)?.color;
  for(const c of SECTION_COLORS){const b=document.createElement('button');b.type='button';b.style.setProperty('--sec',c);b.title='色を変える';b.setAttribute('aria-label','色 '+c);if(c===current)b.classList.add('current');
   b.onclick=()=>{const t=menuTarget;closeMenu();if(!t)return;if(t.type==='section')setSectionColor(doc,t.id,c);else setNotebookColor(doc,t.id,c);changed();renderPages();};colors.append(b);}
  colors.hidden=false;
 } else colors.hidden=true;
 const left=Math.min(rect.left,innerWidth-menu.offsetWidth-8),top=rect.bottom+4+menu.offsetHeight>innerHeight?rect.top-menu.offsetHeight-4:rect.bottom+4;
 menu.style.left=Math.max(4,left)+'px';menu.style.top=Math.max(4,top)+'px';
 $('menu-delete-label').textContent=target.type==='page'?'ページをゴミ箱へ':target.type==='section'?'セクションをゴミ箱へ（中のページも）':'ノートブックをゴミ箱へ（中身ごと）';
 $('menu-delete').disabled=target.type==='notebook'&&doc.notebooks.length<2;
 $('menu-rename').focus();
}
function closeMenu(){$('item-menu').hidden=true;menuTarget?.holder?.classList.remove('menu-open');menuTarget=null;}
document.addEventListener('pointerdown',e=>{if(!$('item-menu').hidden&&!$('item-menu').contains(e.target))closeMenu();},{capture:true});
document.addEventListener('keydown',e=>{if(e.key==='Escape'&&!$('item-menu').hidden)closeMenu();},{capture:true});
document.querySelector('.sidebar').addEventListener('contextmenu',e=>{
 const t=e.target instanceof Element?e.target:null;const pb=t?.closest('.page-button'),st=t?.closest('.section-tab'),nb=t?.closest('.notebook-button');
 const at={left:e.clientX,top:e.clientY,bottom:e.clientY};
 if(pb){e.preventDefault();openMenu({type:'page',id:pb.dataset.pageId,label:pageById(pb.dataset.pageId)?.title||''},at,pb.parentElement);}
 else if(st){e.preventDefault();openMenu({type:'section',id:st.dataset.sectionId,label:sectionOf(doc,st.dataset.sectionId)?.name||''},at,st.parentElement);}
 else if(nb){e.preventDefault();openMenu({type:'notebook',id:nb.dataset.notebookId,label:notebookOf(doc,nb.dataset.notebookId)?.name||''},at,nb.parentElement);}
});
$('menu-rename').onclick=()=>{const t=menuTarget;closeMenu();if(!t)return;
 if(t.type==='page')showForm({kind:'rename-page',id:t.id},'ページの名前の変更',pageById(t.id)?.title||'','変更');
 else if(t.type==='section')showForm({kind:'rename-section',id:t.id},'セクションの名前の変更',sectionOf(doc,t.id)?.name||'','変更');
 else showForm({kind:'rename-notebook',id:t.id},'ノートブックの名前の変更',notebookOf(doc,t.id)?.name||'','変更');
};
$('menu-delete').onclick=()=>{const t=menuTarget;closeMenu();if(!t)return;
 finish();
 const entry=t.type==='page'?deletePage(doc,t.id):t.type==='section'?deleteSection(doc,t.id):deleteNotebook(doc,t.id);
 if(!entry){if(t.type==='notebook')message('最後のノートブックは削除できません。');return;}
 histories.delete(t.id);selectedSectionId=null;showPage();changed();
 const kind={page:'ページ',section:'セクション',notebook:'ノートブック'}[t.type];
 message(kind+'「'+(entry.name||'名称未設定')+'」をゴミ箱へ移動しました。左下の「ゴミ箱」から元に戻せます。');
};
const DEFAULT_NAME='名称未設定';
function uniqueIn(names,base=DEFAULT_NAME){let name=base,n=2;while(names.includes(name))name=base+' '+n++;return name;}
function showForm(mode,title,value,submitLabel) {
 formMode=mode;$('form-title').textContent=title;$('form-submit-label').textContent=submitLabel;
 const forPage=mode.kind==='rename-page'||mode.kind==='new-page';
 $('new-category-name').placeholder=(forPage?'ページの名前':mode.kind.includes('notebook')?'ノートブックの名前':'セクションの名前')+'（空欄なら「'+DEFAULT_NAME+'」）';$('new-category-name').maxLength=forPage?120:60;
 $('new-category').hidden=false;$('new-category-name').value=value;$('new-category-name').focus();$('new-category-name').select();
}
// ---- trash view ----
function renderTrash() {
 const back=document.createElement('button');back.type='button';back.className='trash-back';back.append(icon('back'),'ページ一覧へ戻る');back.onclick=()=>{view='pages';renderPages();};
 $('pages').append(back);
 const items=[...(doc.trash||[])].reverse();
 if(!items.length){const empty=document.createElement('div');empty.className='trash-empty';empty.textContent='ゴミ箱は空です';$('pages').append(empty);return;}
 for(const t of items){
  const item=document.createElement('div');item.className='trash-item';item.dataset.trashId=t.id;
  const kindIcon={page:'file',section:'folder',category:'folder',notebook:'book'}[t.kind]||'file';
  const kindLabel={section:'セクション',category:'セクション',notebook:'ノートブック'}[t.kind];
  const name=document.createElement('span');name.className='trash-name';name.append(icon(kindIcon),' '+(t.name||'名称未設定')+(kindLabel?'（'+kindLabel+'・'+t.pages.length+'ページ）':''));
  const when=document.createElement('small');when.textContent='削除: '+new Date(t.deletedAt).toLocaleString('ja-JP');
  const row=document.createElement('div');
  const restore=document.createElement('button');restore.type='button';restore.className='restore';restore.append(icon('restore'),'元に戻す');
  restore.onclick=()=>{finish();const e=restoreTrash(doc,t.id);if(!e)return;view='pages';selectedSectionId=null;showPage();changed();message('「'+(e.name||'名称未設定')+'」を元に戻しました。');};
  const purge=document.createElement('button');purge.type='button';purge.className='purge';purge.append(icon('x'),'完全に削除');
  purge.onclick=()=>{if(purge.dataset.armed){purgeTrash(doc,t.id);changed();renderPages();}else{purge.dataset.armed='1';purge.replaceChildren(icon('x'),'もう一度押すと完全に削除');setTimeout(()=>{delete purge.dataset.armed;purge.replaceChildren(icon('x'),'完全に削除');},4000);}};
  row.append(restore,purge);item.append(name,when,row);$('pages').append(item);
 }
 const clear=document.createElement('button');clear.type='button';clear.className='trash-clear';clear.append(icon('trash'),'ゴミ箱を空にする');
 clear.onclick=()=>{
  if(performance.now()-clearArmed<4000){clearArmed=0;const n=emptyTrash(doc);changed();renderPages();message(n+'件を完全に削除しました。');return;}
  clearArmed=performance.now();clear.textContent='もう一度押すと '+(doc.trash||[]).length+' 件を完全に削除します';clear.classList.add('confirm');
  setTimeout(()=>{if(clear.isConnected){clear.textContent='ゴミ箱を空にする';clear.classList.remove('confirm');clearArmed=0;}},4000);
 };
 $('pages').append(clear);
}
$('trash-toggle').onclick=()=>{view=view==='trash'?'pages':'trash';renderPages();};
// ---- sidebar drag & drop (mouse): pages, sections, notebooks ----
const navEl=document.querySelector('.sidebar');
function clearDropMarks(){for(const x of navEl.querySelectorAll('.drop-before,.drop-after,.drop-into'))x.classList.remove('drop-before','drop-after','drop-into');}
function dropTarget(e) {
 const t=e.target instanceof Element?e.target:null;if(!t||!dragging)return null;
 const pb=t.closest('.page-button'),st=t.closest('.section-tab'),nh=t.closest('.notebook-head'),pagesCol=t.closest('.nav-pages');
 const half=(node)=>{const r=node.getBoundingClientRect();return e.clientY<r.top+r.height/2?'drop-before':'drop-after';};
 if(dragging.type==='page'){
  if(pb){if(pb.dataset.pageId===dragging.id)return null;return {mark:pb,cls:half(pb),pageId:pb.dataset.pageId,sectionId:pageById(pb.dataset.pageId)?.sectionId};}
  if(st)return {mark:st,cls:'drop-into',sectionId:st.dataset.sectionId};
  if(pagesCol)return {mark:pagesCol,cls:'drop-into',sectionId:currentSection().id};
  return null;
 }
 if(dragging.type==='section'){
  if(st){if(st.dataset.sectionId===dragging.id)return null;const sec=sectionOf(doc,st.dataset.sectionId);return {mark:st,cls:half(st),sectionId:sec.id,notebookId:sec.notebookId};}
  if(nh){const nb=nh.closest('.notebook');return {mark:nh,cls:'drop-into',notebookId:nb.dataset.notebookId};}
  return null;
 }
 if(dragging.type==='notebook'){
  if(nh){const nb=nh.closest('.notebook');if(nb.dataset.notebookId===dragging.id)return null;return {mark:nh,cls:half(nh),notebookId:nb.dataset.notebookId};}
  return null;
 }
 return null;
}
navEl.addEventListener('dragstart',e=>{
 const t=e.target instanceof Element?e.target:null;const pb=t?.closest('.page-button'),st=t?.closest('.section-tab'),nb=t?.closest('.notebook-button');
 if(pb){dragging={type:'page',id:pb.dataset.pageId};pb.classList.add('dragging');}
 else if(st){dragging={type:'section',id:st.dataset.sectionId};st.classList.add('dragging');}
 else if(nb){dragging={type:'notebook',id:nb.dataset.notebookId};nb.classList.add('dragging');}
 else{e.preventDefault();return;}
 e.dataTransfer.effectAllowed='move';try{e.dataTransfer.setData('text/plain',dragging.type);}catch{}
});
navEl.addEventListener('dragend',()=>{dragging=null;clearDropMarks();for(const x of navEl.querySelectorAll('.dragging'))x.classList.remove('dragging');});
navEl.addEventListener('dragover',e=>{
 if(!dragging)return;const t=dropTarget(e);clearDropMarks();if(!t)return;
 e.preventDefault();e.dataTransfer.dropEffect='move';t.mark.classList.add(t.cls);
});
navEl.addEventListener('dragleave',e=>{if(!navEl.contains(e.relatedTarget))clearDropMarks();});
navEl.addEventListener('drop',e=>{
 if(!dragging)return;e.preventDefault();const t=dropTarget(e),d=dragging;dragging=null;clearDropMarks();if(!t)return;
 let moved=false;
 if(d.type==='page'){
  if(t.cls==='drop-into')moved=movePage(doc,d.id,t.sectionId,null);
  else if(t.cls==='drop-before')moved=movePage(doc,d.id,t.sectionId,t.pageId);
  else{const list=pagesIn(doc,t.sectionId),i=list.findIndex(pg=>pg.id===t.pageId);moved=movePage(doc,d.id,t.sectionId,list[i+1]?list[i+1].id:null);}
  if(moved){touchPages([d.id]);if(d.id===doc.activeId){selectedSectionId=null;breadcrumb();}}
 } else if(d.type==='section'){
  if(t.cls==='drop-into')moved=moveSection(doc,d.id,t.notebookId,null);
  else if(t.cls==='drop-before')moved=moveSection(doc,d.id,t.notebookId,t.sectionId);
  else{const list=sectionsIn(doc,t.notebookId),i=list.findIndex(x=>x.id===t.sectionId);moved=moveSection(doc,d.id,t.notebookId,list[i+1]?list[i+1].id:null);}
 } else {
  if(t.cls==='drop-before')moved=moveNotebook(doc,d.id,t.notebookId);
  else{const i=doc.notebooks.findIndex(x=>x.id===t.notebookId);moved=moveNotebook(doc,d.id,doc.notebooks[i+1]?doc.notebooks[i+1].id:null);}
 }
 if(moved){changed();renderPages();}
});
// ---- forms: new page / section / notebook, renames ----
$('add-notebook').onclick=()=>showForm({kind:'new-notebook'},'新しいノートブック','','作成');
$('new-category-cancel').onclick=()=>{$('new-category').hidden=true;formMode=null;};
function createPageIn(sectionId,title) {
 if(doc.pages.length>=500){message('試作品では500ページまで作れます。');return null;}
 finish();const p=newPage(title,sectionId);doc.pages.push(p);doc.activeId=p.id;selectedSectionId=null;showPage();changed();return p;
}
$('new-category').onsubmit=e=>{
 e.preventDefault();const mode=formMode||{kind:'new-page'};const value=$('new-category-name').value.trim();
 const close=()=>{$('new-category').hidden=true;formMode=null;};
 if(mode.kind==='rename-page'){
  const p=pageById(mode.id);if(!p)return;p.title=value||DEFAULT_NAME;close();
  if(p===page()){$('page-title').value=p.title;breadcrumb();}changed(p);renderPages();return;
 }
 if(mode.kind==='rename-section'){
  const sec=sectionOf(doc,mode.id);if(!sec)return;
  renameSection(doc,mode.id,value||uniqueIn(sectionsIn(doc,sec.notebookId).map(x=>x.name)));close();changed();breadcrumb();renderPages();return;
 }
 if(mode.kind==='rename-notebook'){
  renameNotebook(doc,mode.id,value||uniqueIn(doc.notebooks.map(x=>x.name)));close();changed();breadcrumb();renderPages();return;
 }
 if(mode.kind==='new-section'){
  const nbId=notebookOf(doc,mode.notebookId)?mode.notebookId:doc.notebooks[0].id;
  const sec=addSection(doc,nbId,value||uniqueIn(sectionsIn(doc,nbId).map(x=>x.name)));if(!sec)return;close();collapsedNotebooks.delete(nbId);
  createPageIn(sec.id,DEFAULT_NAME);return;
 }
 if(mode.kind==='new-notebook'){
  const nb=addNotebook(doc,value||uniqueIn(doc.notebooks.map(x=>x.name)));close();
  const sec=addSection(doc,nb.id,'新しいセクション 1');createPageIn(sec.id,DEFAULT_NAME);return;
 }
 // new page in the section shown in the page column
 close();createPageIn(currentSection().id,value||DEFAULT_NAME);
};

function breadcrumb(){const p=page(),sec=sectionOf(doc,p.sectionId),nb=sec&&notebookOf(doc,sec.notebookId);$('breadcrumb').textContent=(nb?nb.name+' › ':'')+(sec?sec.name+' › ':'')+(p.title||'名称未設定');}
function showPage() {
 activeBlock=null;editing=null;selection={strokes:new Set(),blocks:new Set()};selectionLasso=null;ensureLayers(page());
 if(document.activeElement&&sheet.contains(document.activeElement))document.activeElement.blur();
 $('page-title').value=page().title;
 breadcrumb();renderPages();renderPage();renderLayers();syncHistory();
}
// ---- page geometry ----
function growPage(p,needed) {
 const next=Math.min(MAX_HEIGHT,Math.max(p.height,Math.ceil(needed)));
 if(next===p.height)return false;
 p.height=next;if(p===page())layout();return true;
}
function layout() {
 if(!doc)return;
 const p=page();scale=paper.clientWidth/W||1;sheetRectCache=null;
 sheet.style.setProperty('--ui-inverse-scale',1/scale);sheet.style.height=p.height+'px';sheet.style.transform='scale('+scale+')';lassoEl.setAttribute('height',p.height);
 paper.style.height=Math.round(p.height*scale)+'px';
 $('page-size').textContent='ページの高さ '+p.height+' / 最大 '+MAX_HEIGHT;$('grow-page').disabled=!ready||p.height>=MAX_HEIGHT;
 updateViewportCanvas(true);
}
// The ink canvas covers only the part of the page that is on screen (plus a margin), not the
// whole page. A page-sized canvas at high DPI (e.g. 2400 x 12000 px on a Surface at 200 %) is
// too large for GPU rasterisation and every pen segment then repaints the whole bitmap, which
// showed up as a 2-3 second pen lag. Coordinates stay in page space via the canvas transform.
const VIEW_MARGIN=300;
// Drawing quality: 'light' halves the ink resolution and caps the canvas at 2.5 M pixels for
// machines whose browser rasterises the canvas in software (seen as pen lag on a Surface Pro).
let quality='normal';try{quality=localStorage.getItem('yohaku-quality')==='light'?'light':'normal';}catch{}
const qualityLimits=()=>quality==='light'?{dpr:1,pixels:2.5e6}:{dpr:3,pixels:8e6};
// UI size (text and buttons of the chrome, not the page content). Default: 大きめ.
let uiSize='large';try{const v=localStorage.getItem('yohaku-ui-size');if(['normal','large','xlarge'].includes(v))uiSize=v;}catch{}
document.body.dataset.ui=uiSize;$('ui-size').value=uiSize;
$('ui-size').onchange=e=>{uiSize=e.target.value;document.body.dataset.ui=uiSize;try{localStorage.setItem('yohaku-ui-size',uiSize);}catch{}layout();};
$('view-quality').value=quality;
$('view-quality').onchange=e=>{quality=e.target.value==='light'?'light':'normal';try{localStorage.setItem('yohaku-quality',quality);}catch{}updateViewportCanvas(true);message(quality==='light'?'描画を「軽い」にしました。手書きの解像度を下げて、ペンの遅れを減らします。':'描画を「標準」に戻しました。');};
let inkView={top:0,bottom:0,k:1},viewRaf=0;
function viewportRange() {
 const rect=sheet.getBoundingClientRect(),p=page();
 const vt=Math.max(0,Math.floor(-rect.top/scale)),vb=Math.min(p.height,Math.ceil((innerHeight-rect.top)/scale));
 return [Math.min(vt,Math.max(0,p.height-1)),Math.max(vt+1,vb)];
}
function updateViewportCanvas(force=false) {
 if(!doc)return;const p=page();const [vt,vb]=viewportRange();
 if(!force&&vt>=inkView.top&&vb<=inkView.bottom)return;
 const top=Math.max(0,vt-VIEW_MARGIN),bottom=Math.min(p.height,vb+VIEW_MARGIN),h=Math.max(1,bottom-top);
 const q=qualityLimits();let k=scale*Math.min(devicePixelRatio||1,q.dpr);const pixels=W*k*h*k;if(pixels>q.pixels)k*=Math.sqrt(q.pixels/pixels);
 inkView={top,bottom,k};
 canvas.style.top=top+'px';canvas.style.height=h+'px';
 canvas.width=Math.max(1,Math.round(W*k));canvas.height=Math.max(1,Math.round(h*k));
 ctx.setTransform(k,0,0,k,0,-top*k);
 redraw();
}
const onViewportScroll=()=>{if(viewRaf)return;viewRaf=requestAnimationFrame(()=>{viewRaf=0;updateViewportCanvas();});};
window.addEventListener('scroll',onViewportScroll,{passive:true});window.addEventListener('resize',onViewportScroll);
document.getElementById('paper-viewport')?.addEventListener('scroll',onViewportScroll,{passive:true});
new ResizeObserver(()=>{if(paper.clientWidth!==lastPaperWidth){lastPaperWidth=paper.clientWidth;layout();}}).observe(paper);
let sheetRectCache=null;
function sheetRect(){if(!sheetRectCache){sheetRectCache=sheet.getBoundingClientRect();requestAnimationFrame(()=>{sheetRectCache=null;});}return sheetRectCache;}
function coordinates(e) {
 const rect=sheetRect();
 return [(e.clientX-rect.left)/scale,(e.clientY-rect.top)/scale,clamp(e.pressure||.5,0,1)];
}
function inkPoint(e) {
 const [x,y,pr]=coordinates(e),p=page();
 if(y>p.height-100)growPage(p,y+400);
 return [clamp(x,0,W),clamp(y,0,p.height),pr];
}
// ---- ink ----
function dot(p,r,c,g=ctx) {g.fillStyle=c;g.beginPath();g.arc(p[0],p[1],r,0,Math.PI*2);g.fill();}
function segment(a,b,s,g=ctx) {
 const wa=inkWidth(s.width,a[2],s.pressure),wb=inkWidth(s.width,b[2],s.pressure);
 g.strokeStyle=s.color;g.lineWidth=(wa+wb)/2;g.lineCap='round';g.lineJoin='round';
 g.beginPath();g.moveTo(a[0],a[1]);g.lineTo(b[0],b[1]);g.stroke();
}
function drawStroke(g,s) {
 const pts=s.points;
 if(pts.length===1){dot(pts[0],inkWidth(s.width,pts[0][2],s.pressure)/2,s.color,g);return;}
 if(!s.pressure){
  g.strokeStyle=s.color;g.lineWidth=s.width;g.lineCap='round';g.lineJoin='round';
  g.beginPath();g.moveTo(pts[0][0],pts[0][1]);for(let i=1;i<pts.length;i++)g.lineTo(pts[i][0],pts[i][1]);g.stroke();return;
 }
 g.lineCap='round';g.lineJoin='round';g.strokeStyle=s.color;
 // pressure: group consecutive segments whose width barely changes into one path
 let i=1,w=(inkWidth(s.width,pts[0][2],true)+inkWidth(s.width,pts[1][2],true))/2;
 while(i<pts.length){
  g.lineWidth=w;g.beginPath();g.moveTo(pts[i-1][0],pts[i-1][1]);
  let j=i;
  for(;j<pts.length;j++){const wj=(inkWidth(s.width,pts[j-1][2],true)+inkWidth(s.width,pts[j][2],true))/2;if(Math.abs(wj-w)>Math.max(.35,w*.12))break;g.lineTo(pts[j][0],pts[j][1]);}
  if(j===i){g.lineTo(pts[i][0],pts[i][1]);j=i+1;}
  g.stroke();i=j;if(i<pts.length)w=(inkWidth(s.width,pts[i-1][2],true)+inkWidth(s.width,pts[i][2],true))/2;
 }
}
// Bounding box per stroke [x0,y0,x1,y1] (with ink margin), cached and refreshed when points are added.
const bboxCache=new WeakMap();
function strokeBBox(s) {
 let r=bboxCache.get(s);
 if(!r||r[4]!==s.points.length){
  let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity;
  for(const pt of s.points){if(pt[0]<x0)x0=pt[0];if(pt[0]>x1)x1=pt[0];if(pt[1]<y0)y0=pt[1];if(pt[1]>y1)y1=pt[1];}
  const m=s.width*2;r=[x0-m,y0-m,x1+m,y1+m,s.points.length];bboxCache.set(s,r);
 }
 return r;
}
const boxesTouch=(a,b)=>!(a[2]<b[0]||a[0]>b[2]||a[3]<b[1]||a[1]>b[3]);
const boxUnion=(a,b)=>a?[Math.min(a[0],b[0]),Math.min(a[1],b[1]),Math.max(a[2],b[2]),Math.max(a[3],b[3])]:[b[0],b[1],b[2],b[3]];
function drawStrokes(g,strokes,clipBox=null) {
 for(const s of strokes){
  const bb=strokeBBox(s);if(bb[3]<inkView.top||bb[1]>inkView.bottom)continue;
  if(clipBox&&!boxesTouch(bb,clipBox))continue;
  drawStroke(g,s);
 }
}
// Layers are painted bottom to top. A translucent layer is drawn on an offscreen canvas
// first so overlapping strokes inside it do not darken each other.
function redraw() {
 if(!doc)return;const p=page();ensureLayers(p);const t0=performance.now();
 ctx.save();ctx.setTransform(1,0,0,1,0,0);ctx.clearRect(0,0,canvas.width,canvas.height);ctx.restore();
 for(const L of p.layers){
  if(!L.visible)continue;const strokes=p.strokes.filter(s=>s.layer===L.id);if(!strokes.length)continue;
  if(L.opacity>=1){drawStrokes(ctx,strokes);continue;}
  if(off.width!==canvas.width||off.height!==canvas.height){off.width=canvas.width;off.height=canvas.height;}
  octx.setTransform(1,0,0,1,0,0);octx.clearRect(0,0,off.width,off.height);octx.setTransform(inkView.k,0,0,inkView.k,0,-inkView.top*inkView.k);
  drawStrokes(octx,strokes);
  ctx.save();ctx.setTransform(1,0,0,1,0,0);ctx.globalAlpha=L.opacity;ctx.drawImage(off,0,0);ctx.restore();
 }
 updateHint();renderSelection();perf.redraw=Math.round(performance.now()-t0);
}
// Redraw only a rectangle of the page (page coordinates). Used by the eraser so that removing a
// bit of ink does not repaint the whole visible strip.
function redrawRegion(box) {
 if(!doc||!box)return;const p=page();ensureLayers(p);const t0=performance.now();
 const x0=Math.max(0,box[0]),y0=Math.max(inkView.top,box[1]),x1=Math.min(W,box[2]),y1=Math.min(inkView.bottom,box[3]);
 if(x1<=x0||y1<=y0)return;const clip=[x0,y0,x1,y1];
 ctx.save();ctx.beginPath();ctx.rect(x0,y0,x1-x0,y1-y0);ctx.clip();ctx.clearRect(x0,y0,x1-x0,y1-y0);
 for(const L of p.layers){
  if(!L.visible)continue;const strokes=p.strokes.filter(s=>s.layer===L.id&&boxesTouch(strokeBBox(s),clip));if(!strokes.length)continue;
  if(L.opacity>=1){drawStrokes(ctx,strokes,clip);continue;}
  if(off.width!==canvas.width||off.height!==canvas.height){off.width=canvas.width;off.height=canvas.height;}
  octx.save();octx.setTransform(inkView.k,0,0,inkView.k,0,-inkView.top*inkView.k);octx.beginPath();octx.rect(x0,y0,x1-x0,y1-y0);octx.clip();octx.clearRect(x0,y0,x1-x0,y1-y0);drawStrokes(octx,strokes,clip);octx.restore();
  ctx.save();ctx.setTransform(1,0,0,1,0,0);ctx.globalAlpha=L.opacity;ctx.drawImage(off,0,0);ctx.restore();
 }
 ctx.restore();perf.redraw=Math.round(performance.now()-t0);
}
// The layer that receives pen, eraser and selection. Null (with a message) when it is hidden or locked.
function editableLayer(quiet=false) {
 const p=page();ensureLayers(p);const L=activeLayerOf(p);
 if(L.visible&&!L.locked)return L;
 if(!quiet)message('レイヤー「'+L.name+'」は'+(L.locked?'ロック中':'非表示')+'です。右のレイヤー一覧で解除するか、別のレイヤーの行をクリックしてください。');
 return null;
}
function updateHint(){const p=page();$('empty-hint').hidden=p.strokes.length>0||p.blocks.length>0;}
const eraserRadius=()=>Math.max(.5,eraserSize/2);
function erase(a,b) {
 const p=page(),r=eraserRadius(),next=[],lid=p.activeLayer;let changed=false,dirty=null;
 const reach=[Math.min(a[0],b[0])-r-2,Math.min(a[1],b[1])-r-2,Math.max(a[0],b[0])+r+2,Math.max(a[1],b[1])+r+2];
 for(const s of p.strokes){
  if(s.layer!==lid){next.push(s);continue;}
  const bb=strokeBBox(s);if(!boxesTouch(bb,reach)){next.push(s);continue;}
  if(eraserMode==='whole'){if(hitStroke(s,a,b,r)){changed=true;dirty=boxUnion(dirty,bb);}else next.push(s);}
  else{const parts=erasePart(s,a,b,r);if(parts.length!==1||parts[0]!==s){changed=true;dirty=boxUnion(dirty,bb);}next.push(...parts);}
 }
 if(changed){p.strokes=next;gesture.changed=true;gesture.dirty=boxUnion(gesture.dirty,dirty);}
}
function flushEraseRedraw(){if(gesture&&gesture.dirty){const box=gesture.dirty;gesture.dirty=null;redrawRegion(box);}}
function startInk(e) {
 const L=editableLayer();if(!L)return;
 const point=inkPoint(e);
 const erasing=tool==='eraser'||(e.pointerType==='pen'&&(e.button===5||(e.buttons&32)!==0||(e.buttons&2)!==0));
 gesture={type:'ink',id:e.pointerId,pageId:doc.activeId,before:snapshot(page()),erase:erasing,last:point,changed:false,opacity:L.opacity};
 try{sheet.setPointerCapture(e.pointerId);}catch{}
 if(erasing){erase(point,point);flushEraseRedraw();}
 else {
  const stroke={color,width,pressure:e.pointerType==='pen'&&$('pressure').checked,points:[point],layer:L.id};
  page().strokes=[...page().strokes,stroke];gesture.stroke=stroke;gesture.changed=true;
  ctx.globalAlpha=L.opacity;dot(point,inkWidth(width,point[2],stroke.pressure)/2,color);ctx.globalAlpha=1;
  // Redraw everything at the end only when the live drawing cannot be the final picture:
  // the layer is translucent (joints would darken) or another visible layer sits above it.
  const above=page().layers.slice(page().layers.indexOf(L)+1).some(x=>x.visible);
  gesture.needsRedraw=L.opacity<1||above;
 }
}
const perf={finish:0,redraw:0,points:0};let statusRaf=0,statusEvent=null;
function inputStatus(e){
 statusEvent=e;if(statusRaf)return;
 statusRaf=requestAnimationFrame(()=>{statusRaf=0;const ev=statusEvent;if(!ev)return;
  const base=ev.pointerType==='pen'?'ペン入力 · 筆圧 '+(ev.pressure||0).toFixed(2):ev.pointerType==='touch'?'タッチ':'マウス入力';
  $('input-status').textContent=base+(perf.points?' · 前の線 '+perf.points+'点 / 確定 '+perf.finish+'ms / 描画 '+perf.redraw+'ms':'');});
}
// ---- selection ----
function strokeBounds(s) {
 let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity;
 for(const pt of s.points){const r=inkWidth(s.width,pt[2],s.pressure)/2;x0=Math.min(x0,pt[0]-r);y0=Math.min(y0,pt[1]-r);x1=Math.max(x1,pt[0]+r);y1=Math.max(y1,pt[1]+r);}
 return {x0,y0,x1,y1};
}
function selectionBounds(p=page()) {
 let b=null;const add=r=>{b=b?{x0:Math.min(b.x0,r.x0),y0:Math.min(b.y0,r.y0),x1:Math.max(b.x1,r.x1),y1:Math.max(b.y1,r.y1)}:{...r};};
 for(const s of p.strokes)if(selection.strokes.has(s))add(strokeBounds(s));
 for(const bl of p.blocks)if(selection.blocks.has(bl.id))add({x0:bl.x,y0:bl.y,x1:bl.x+bl.width,y1:bl.y+bl.height});
 return b;
}
const selectionEmpty=()=>selection.strokes.size===0&&selection.blocks.size===0;
function clearSelection(){selection={strokes:new Set(),blocks:new Set()};selectionLasso=null;renderSelection();}
function renderSelection() {
 if(!doc)return;const p=page();
 selection.strokes=new Set([...selection.strokes].filter(s=>p.strokes.includes(s)));
 selection.blocks=new Set([...selection.blocks].filter(id=>p.blocks.some(b=>b.id===id)));
 const b=tool==='select'?selectionBounds(p):null;
 if(!b)selectionLasso=null;
 // 投げ縄で選んだときは、囲んだ形そのものを点線で示す（四角い枠は出さない）
 selectionEl.hidden=!b||!!selectionLasso;
 if(b){selectionEl.style.left=(b.x0-6)+'px';selectionEl.style.top=(b.y0-6)+'px';selectionEl.style.width=(b.x1-b.x0+12)+'px';selectionEl.style.height=(b.y1-b.y0+12)+'px';}
 if(!gesture||gesture.type!=='lasso'){lassoEl.classList.toggle('settled',!!selectionLasso);renderLasso(selectionLasso||[]);}
 for(const el of blocksLayer.children)el.classList.toggle('selected',selection.blocks.has(el.dataset.id));
 const n=selection.strokes.size+selection.blocks.size;
 if(tool==='select')$('tool-hint').textContent=n?n+'個を選択中。ドラッグまたは矢印キーで移動、Deleteで削除、Escで解除':hints.select;
}
function insideSelection(x,y) {
 if(selectionEmpty())return false;
 if(selectionLasso)return pointInPolygon([x,y],selectionLasso);
 const b=selectionBounds();
 return !!b&&x>=b.x0-6&&x<=b.x1+6&&y>=b.y0-6&&y<=b.y1+6;
}
// Move the selected strokes/blocks by (dx,dy) relative to `base` (arrays captured before the move).
function translateSelection(p,base,dx,dy) {
 dx=Math.round(clamp(dx,-base.bounds.x0,W-base.bounds.x1));dy=Math.round(clamp(dy,-base.bounds.y0,MAX_HEIGHT-base.bounds.y1));
 const moved=new Map();
 for(const s of base.selStrokes)moved.set(s,{...s,points:s.points.map(pt=>[pt[0]+dx,pt[1]+dy,pt[2]])});
 p.strokes=base.strokes.map(s=>moved.get(s)||s);
 p.blocks=base.blocks.map(b=>base.selBlocks.has(b.id)?{...b,x:b.x+dx,y:b.y+dy}:b);
 selection={strokes:new Set(moved.values()),blocks:new Set(base.selBlocks)};
 selectionLasso=base.lasso?base.lasso.map(q=>[q[0]+dx,q[1]+dy]):null;
 growPage(p,base.bounds.y1+dy+60);
 return dx!==0||dy!==0;
}
function selectionBase(p=page()) {
 return {strokes:p.strokes,blocks:p.blocks,selStrokes:[...selection.strokes],selBlocks:new Set(selection.blocks),bounds:selectionBounds(p),lasso:selectionLasso?selectionLasso.map(q=>[q[0],q[1]]):null};
}
function nudgeSelection(dx,dy) {
 if(selectionEmpty())return;
 const p=page(),before=snapshot(p),base=selectionBase(p);
 if(!translateSelection(p,base,dx,dy))return;
 const now=performance.now();
 if(now-arrowBatch<800)changed(p);else commit(before,p);
 arrowBatch=now;redraw();renderBlocks();renderSelection();
}
function deleteSelection() {
 if(selectionEmpty())return;
 const p=page(),before=snapshot(p);
 p.strokes=p.strokes.filter(s=>!selection.strokes.has(s));p.blocks=p.blocks.filter(b=>!selection.blocks.has(b.id));
 clearSelection();commit(before,p);renderPage();
}
function applyMarquee(r,additive) {
 const p=page();if(!additive)selection={strokes:new Set(),blocks:new Set()};selectionLasso=null;
 const L=editableLayer(true),lid=L?L.id:null;
 for(const s of p.strokes)if(s.layer===lid&&s.points.some(pt=>pt[0]>=r.x0&&pt[0]<=r.x1&&pt[1]>=r.y0&&pt[1]<=r.y1))selection.strokes.add(s);
 for(const b of p.blocks)if(b.x>=r.x0&&b.x+b.width<=r.x1&&b.y>=r.y0&&b.y+b.height<=r.y1)selection.blocks.add(b.id);
 renderSelection();
}
function applyLasso(polygon,additive) {
 const p=page(),before=snapshot(p);
 if(!additive)selection={strokes:new Set(),blocks:new Set()};
 let split=false;const next=[];const L=editableLayer(true),lid=L?L.id:null;
 for(const s of p.strokes){
  if(s.layer!==lid){next.push(s);continue;}
  const r=splitByPolygon(s,polygon);
  if(r.inside.length&&r.inside[0]!==s)split=true;
  next.push(...r.outside,...r.inside);for(const f of r.inside)selection.strokes.add(f);
 }
 for(const b of p.blocks)if(pointInPolygon([b.x+b.width/2,b.y+b.height/2],polygon))selection.blocks.add(b.id);
 if(split){p.strokes=next;commit(before,p);redraw();}
 renderSelection();
}
function renderLasso(points) {
 lassoEl.toggleAttribute('hidden',points.length<2);
 lassoEl.querySelector('path').setAttribute('d',points.length?'M'+points.map(pt=>pt[0].toFixed(1)+' '+pt[1].toFixed(1)).join('L')+'Z':'');
}
function strokeAt(x,y) {
 const p=page(),r=6/scale,L=editableLayer(true);if(!L)return null;
 for(let i=p.strokes.length-1;i>=0;i--)if(p.strokes[i].layer===L.id&&hitStroke(p.strokes[i],[x,y],[x,y],r))return p.strokes[i];
 return null;
}
function startDrag(e,point) {
 gesture={type:'drag',id:e.pointerId,pageId:doc.activeId,before:snapshot(page()),start:point,base:selectionBase(),changed:false};
 try{sheet.setPointerCapture(e.pointerId);}catch{}
}
// Pen / eraser cursor: a circle showing the real size of the mark that will be made.
function updateEraserCursor(e) {
 const penInk=tool==='pen'||(tool==='text'&&e.pointerType==='pen'&&$('auto-pen').checked);
 if((tool!=='eraser'&&!penInk)||e.pointerType==='touch'){eraserCursor.hidden=true;return;}
 const [x,y]=coordinates(e);let d;
 if(tool==='eraser')d=eraserRadius()*2;
 else {
  const usePressure=e.pointerType==='pen'&&$('pressure').checked;
  d=inkWidth(width,usePressure?(e.buttons?clamp(e.pressure||0,0,1):.5):.5,usePressure);
  eraserCursor.style.setProperty('--ink',color.toLowerCase()==='#ffffff'?'#8a8f8c':color);
 }
 eraserCursor.classList.toggle('pen',tool!=='eraser');
 d=Math.max(d,8/scale);
 eraserCursor.hidden=false;eraserCursor.style.left=x+'px';eraserCursor.style.top=y+'px';eraserCursor.style.width=d+'px';eraserCursor.style.height=d+'px';
}
// ---- blocks ----
function updateBlock(p,id,patch){p.blocks=p.blocks.map(b=>b.id===id?{...b,...patch}:b);}
function blockOf(id,p=page()){return p.blocks.find(b=>b.id===id);}
function setActive(id) {
 activeBlock=id;
 for(const el of blocksLayer.children)el.classList.toggle('active',el.dataset.id===id);
}
function autosize(el,block) {
 const ed=el.querySelector('.editor');if(!ed)return;
 const h=clamp(Math.ceil(ed.offsetHeight)+2,40,MAX_HEIGHT-block.y);
 if(h!==block.height){const p=page();updateBlock(p,block.id,{height:h});growPage(p,block.y+h+60);}
}
function syncEditor(ed,block) {
 const runs=blockRuns(block),key=JSON.stringify(runs);
 if(lastRuns.get(ed)!==key){runsToDom(ed,runs);lastRuns.set(ed,key);}
 ed.dataset.empty=String(!block.text);
}
function renderBlocks() {
 const p=page(),seen=new Set();
 for(const b of p.blocks){
  seen.add(b.id);
  let el=blocksLayer.querySelector('[data-id="'+b.id+'"]');
  if(!el){
   el=document.createElement('div');el.dataset.id=b.id;el.dataset.pageId=p.id;el.className='block '+b.type;
   const bar=document.createElement('div');bar.className='block-bar';
   const grip=document.createElement('button');grip.type='button';grip.className='grip';grip.append(icon('move'),'移動');grip.setAttribute('aria-label',(b.type==='image'?'画像':'入力欄')+'を移動');
   const remove=document.createElement('button');remove.type='button';remove.className='remove';remove.append(icon('x'));remove.setAttribute('aria-label',(b.type==='image'?'画像':'入力欄')+'を削除');remove.title='削除';
   remove.onclick=()=>removeBlock(b.id);
   bar.append(grip,remove);el.append(bar);
   if(b.type==='text'){
    const ed=document.createElement('div');ed.className='editor';ed.contentEditable='true';ed.dataset.placeholder='ここに入力…';ed.spellcheck=false;
    ed.setAttribute('role','textbox');ed.setAttribute('aria-multiline','true');ed.setAttribute('aria-label','テキスト');
    ed.addEventListener('beforeinput',()=>{if(!editing||editing.id!==b.id)editing={id:b.id,before:snapshot(page()),committed:false};});
    ed.addEventListener('input',()=>{
     const cur=blockOf(b.id);if(!cur)return;
     const runs=domToRuns(ed),text=runsToText(runs);
     if(text.length>200000){message('文字数が上限（20万字）に達しました。');runsToDom(ed,blockRuns(cur));return;}
     lastRuns.set(ed,JSON.stringify(runs));updateBlock(page(),b.id,{text,runs});ed.dataset.empty=String(!text);autosize(el,blockOf(b.id));
     if(editing&&editing.id===b.id&&!editing.committed){editing.committed=true;commit(editing.before);}else changed();
     updateHint();
    });
    ed.addEventListener('paste',e=>{
     const files=[...(e.clipboardData?.files||[])];if(files.some(f=>f.type.startsWith('image/')))return;
     e.preventDefault();const t=e.clipboardData?.getData('text/plain');if(t)document.execCommand('insertText',false,t);
    });
    ed.addEventListener('focus',()=>setActive(b.id));
    ed.addEventListener('blur',()=>{
     editing=null;const owner=pageById(el.dataset.pageId);const cur=owner&&blockOf(b.id,owner);
     if(cur&&cur.text===''){owner.blocks=owner.blocks.filter(x=>x.id!==b.id);if(activeBlock===b.id)activeBlock=null;changed(owner);if(owner===page())renderPage();}
    });
    el.append(ed);
   } else {
    const img=document.createElement('img');img.src=b.src;img.alt=b.name||'貼り付けた画像';img.draggable=false;el.append(img);
   }
   const rs=document.createElement('div');rs.className='resize';rs.setAttribute('aria-label',b.type==='image'?'大きさを変える':'幅を変える');el.append(rs);
   blocksLayer.append(el);
  }
  el.style.left=b.x+'px';el.style.top=b.y+'px';el.style.width=b.width+'px';
  if(b.type==='image')el.style.height=b.height+'px';
  else {
   const ed=el.querySelector('.editor');syncEditor(ed,b);
   const sizeKey=b.width+':'+lastRuns.get(ed).length;
   if(el.dataset.sized!==sizeKey){el.dataset.sized=sizeKey;autosize(el,b);}
  }
  el.classList.toggle('active',b.id===activeBlock);
 }
 for(const el of [...blocksLayer.children])if(!seen.has(el.dataset.id))el.remove();
 updateHint();
}
function renderPage(){layout();renderBlocks();}
function removeBlock(id) {
 const p=page();if(!blockOf(id,p))return;
 const before=snapshot(p);p.blocks=p.blocks.filter(b=>b.id!==id);if(activeBlock===id)activeBlock=null;
 commit(before);renderPage();
}
function createTextBlock(x,y) {
 const p=page(),before=snapshot(p);
 const bx=clamp(Math.round(x)-12,0,W-240),by=clamp(Math.round(y)-14,0,MAX_HEIGHT-60);
 const block=newTextBlock(bx,by,'');block.width=Math.min(640,W-bx-24);block.height=44;
 p.blocks=[...p.blocks,block];growPage(p,by+block.height+60);
 commit(before);activeBlock=block.id;renderPage();
 blocksLayer.querySelector('[data-id="'+block.id+'"] .editor')?.focus();
}
function nextFreeY(p) {
 let y=40;for(const b of p.blocks)y=Math.max(y,b.y+b.height);for(const s of p.strokes)for(const pt of s.points)y=Math.max(y,pt[1]);
 return y+32;
}
// ---- images ----
async function prepareImage(file) {
 if(!/^image\/(png|jpeg|webp)$/.test(file.type))throw new Error('PNG・JPEG・WebP の画像を選んでください。');
 if(file.size>25*1024*1024)throw new Error('25MB以下の画像を選んでください。');
 const bitmap=await createImageBitmap(file);
 const ratio=Math.min(1,1600/Math.max(bitmap.width,bitmap.height));
 const c=document.createElement('canvas');c.width=Math.max(1,Math.round(bitmap.width*ratio));c.height=Math.max(1,Math.round(bitmap.height*ratio));
 c.getContext('2d').drawImage(bitmap,0,0,c.width,c.height);bitmap.close?.();
 const src=c.toDataURL(file.type==='image/png'?'image/png':'image/jpeg',.9);
 if(!/^data:image\/(png|jpeg);base64,/.test(src)||src.length>16000000)throw new Error('画像を変換できませんでした。');
 return {src,width:c.width,height:c.height};
}
async function insertImages(files,point) {
 if(document.body.classList.contains('reading')){message('画像を貼るには「編集に戻る」を押してください。');return;}
 const targetId=doc.activeId;let count=0;
 for(const file of files){
  try{
   const img=await prepareImage(file);const p=pageById(targetId);
   if(!p)throw new Error('挿入先のページが見つかりません。');
   const total=doc.pages.reduce((n,pg)=>n+pg.blocks.reduce((m,b)=>m+(b.src?.length||0),0),0);
   if(total+img.src.length>60000000)throw new Error('試作品の画像容量の上限に達しました。');
   const w=clamp(Math.min(img.width,600),40,W-48),h=Math.max(24,Math.round(w*img.height/img.width));
   const x=point&&count===0?clamp(Math.round(point[0]),0,W-w):64;
   const y=point&&count===0?clamp(Math.round(point[1]),0,MAX_HEIGHT-h):nextFreeY(p);
   if(y+h>MAX_HEIGHT)throw new Error('ページの下端に空きがありません。新しいページに貼り付けてください。');
   const before=snapshot(p);
   p.blocks=[...p.blocks,{id:crypto.randomUUID(),type:'image',x,y,width:w,height:h,src:img.src,name:(file.name||'image').slice(0,100)}];
   growPage(p,y+h+80);commit(before,p);activeBlock=p.blocks.at(-1).id;count++;
   if(p===page())renderPage();
  }catch(error){message('画像を追加できませんでした。'+(error.message||''));}
 }
}
$('add-image').onclick=()=>{$('image-file').value='';$('image-file').click();};
$('image-file').onchange=e=>{const files=[...e.target.files];if(files.length)insertImages(files,null);};
document.addEventListener('paste',e=>{
 if(!ready)return;const files=[...(e.clipboardData?.files||[])].filter(f=>f.type.startsWith('image/'));
 if(!files.length)return;e.preventDefault();insertImages(files,null);
});
window.addEventListener('dragover',e=>e.preventDefault());
window.addEventListener('drop',e=>{
 e.preventDefault();if(!ready)return;
 const files=[...(e.dataTransfer?.files||[])].filter(f=>f.type.startsWith('image/'));if(!files.length)return;
 const inside=sheet.contains(e.target);insertImages(files,inside?coordinates(e):null);
});
// ---- pointer handling on the sheet ----
sheet.tabIndex=-1;
// Pen proximity: while a pen hovers over or touches the page, mark the sheet so CSS turns off
// touch panning (a pen must draw, not scroll). Fingers get scrolling back 1.2 s after the pen leaves.
let penNearTimer=0;
function penNear(e) {
 if(e.pointerType!=='pen')return;
 if(!sheet.classList.contains('pen-near'))sheet.classList.add('pen-near');
 clearTimeout(penNearTimer);penNearTimer=setTimeout(()=>sheet.classList.remove('pen-near'),1200);
}
for(const ev of ['pointerover','pointerenter','pointermove','pointerdown'])sheet.addEventListener(ev,penNear,{capture:true,passive:true});
sheet.addEventListener('pointerleave',e=>{if(e.pointerType==='pen'){clearTimeout(penNearTimer);penNearTimer=setTimeout(()=>sheet.classList.remove('pen-near'),400);}});
sheet.addEventListener('pointerdown',e=>{
 if(!ready)return;
 if(gesture){if(gesture.id===e.pointerId)return;finish();}
 const t=e.target instanceof Element?e.target:null;
 const grip=t?.closest('.grip'),resize=t?.closest('.resize'),blockEl=t?.closest('.block');
 if(blockEl&&tool==='text')setActive(blockEl.dataset.id);
 if(grip||resize){
  if(e.pointerType==='mouse'&&e.button!==0)return;
  e.preventDefault();const b=blockOf(blockEl.dataset.id);if(!b)return;
  gesture={type:grip?'move':'resize',id:e.pointerId,pageId:doc.activeId,blockId:b.id,before:snapshot(page()),start:coordinates(e),origin:{...b},changed:false};
  try{sheet.setPointerCapture(e.pointerId);}catch{}
  return;
 }
 if(e.pointerType==='mouse'&&e.button!==0)return;
 if(tool==='select'){
  const point=coordinates(e),additive=e.shiftKey;sheet.focus({preventScroll:true});
  if(blockEl){
   e.preventDefault();const id=blockEl.dataset.id;
   if(!selection.blocks.has(id)){if(!additive)selection={strokes:new Set(),blocks:new Set()};selection.blocks.add(id);selectionLasso=null;}
   renderSelection();startDrag(e,point);return;
  }
  if(insideSelection(point[0],point[1])){e.preventDefault();startDrag(e,point);return;}
  if(e.pointerType==='touch')return;
  e.preventDefault();
  // 四角モードだけ、線の上で押したらその線をつかむ。投げ縄は線の上から囲み始めてよい。
  const hit=selectMode==='lasso'?null:strokeAt(point[0],point[1]);
  if(hit){if(!additive)selection={strokes:new Set(),blocks:new Set()};selection.strokes.add(hit);selectionLasso=null;renderSelection();startDrag(e,point);return;}
  if(!additive)clearSelection();else selectionLasso=null;
  if(selectMode==='lasso'){
   lassoEl.classList.remove('settled');
   gesture={type:'lasso',id:e.pointerId,pageId:doc.activeId,points:[point],additive,changed:false};
   try{sheet.setPointerCapture(e.pointerId);}catch{}
   renderLasso(gesture.points);return;
  }
  gesture={type:'marquee',id:e.pointerId,pageId:doc.activeId,start:point,last:point,additive,changed:false};
  try{sheet.setPointerCapture(e.pointerId);}catch{}
  marqueeEl.hidden=false;marqueeEl.style.left=point[0]+'px';marqueeEl.style.top=point[1]+'px';marqueeEl.style.width='0px';marqueeEl.style.height='0px';
  return;
 }
 if(e.pointerType==='touch')return;
 const ink=tool!=='text'||(e.pointerType==='pen'&&$('auto-pen').checked);
 if(!ink)return;
 e.preventDefault();startInk(e);inputStatus(e);
},{capture:true});
sheet.addEventListener('pointermove',e=>{
 if(!gesture)updateEraserCursor(e);
 if(!gesture||e.pointerId!==gesture.id)return;
 e.preventDefault();
 if(gesture.type==='drag'){
  const [x,y]=coordinates(e),p=page();
  if(translateSelection(p,gesture.base,x-gesture.start[0],y-gesture.start[1]))gesture.changed=true;
  redraw();renderBlocks();renderSelection();return;
 }
 if(gesture.type==='lasso'){
  let events=e.getCoalescedEvents?.();if(!events?.length)events=[e];
  for(const event of events){const [x,y]=coordinates(event);const pt=[clamp(x,0,W),clamp(y,0,page().height)];const last=gesture.points.at(-1);if(Math.hypot(pt[0]-last[0],pt[1]-last[1])>=1.5)gesture.points.push(pt);}
  renderLasso(gesture.points);return;
 }
 if(gesture.type==='marquee'){
  const [x,y]=coordinates(e);gesture.last=[clamp(x,0,W),clamp(y,0,page().height)];
  const x0=Math.min(gesture.start[0],gesture.last[0]),y0=Math.min(gesture.start[1],gesture.last[1]);
  marqueeEl.style.left=x0+'px';marqueeEl.style.top=y0+'px';marqueeEl.style.width=Math.abs(gesture.last[0]-gesture.start[0])+'px';marqueeEl.style.height=Math.abs(gesture.last[1]-gesture.start[1])+'px';
  return;
 }
 if(gesture.type==='ink'){
  updateEraserCursor(e);
  let events=e.getCoalescedEvents?.();if(!events?.length)events=[e];
  for(const event of events){
   const point=inkPoint(event);
   if(gesture.erase)erase(gesture.last,point);
   else {gesture.stroke.points.push(point);ctx.globalAlpha=gesture.opacity;segment(gesture.last,point,gesture.stroke);ctx.globalAlpha=1;}
   gesture.last=point;
  }
  if(gesture.erase)flushEraseRedraw();
  inputStatus(e);return;
 }
 const p=page(),b=blockOf(gesture.blockId);if(!b)return;
 const [x,y]=coordinates(e),dx=x-gesture.start[0],dy=y-gesture.start[1],o=gesture.origin;
 if(gesture.type==='move'){
  const nx=Math.round(clamp(o.x+dx,0,W-b.width)),ny=Math.round(clamp(o.y+dy,0,MAX_HEIGHT-b.height));
  if(nx===b.x&&ny===b.y)return;
  updateBlock(p,b.id,{x:nx,y:ny});growPage(p,ny+b.height+60);
 } else if(b.type==='text'){
  const nw=Math.round(clamp(o.width+dx,120,W-b.x));if(nw===b.width)return;
  updateBlock(p,b.id,{width:nw});
 } else {
  const nw=Math.round(clamp(o.width+dx,40,W-b.x)),nh=Math.max(24,Math.round(nw*o.height/o.width));
  if(b.y+nh>MAX_HEIGHT||nw===b.width)return;
  updateBlock(p,b.id,{width:nw,height:nh});growPage(p,b.y+nh+60);
 }
 gesture.changed=true;renderBlocks();
});
function finish() {
 if(!gesture)return;
 const completed=gesture;gesture=null;const t0=performance.now();if(completed.stroke)perf.points=completed.stroke.points.length;
 if(sheet.hasPointerCapture?.(completed.id))sheet.releasePointerCapture(completed.id);
 lastInkEnd=performance.now(); // any gesture: the click that follows it must not create a text block
 if(completed.type==='lasso'){
  renderLasso([]);lassoEl.setAttribute('hidden','');
  if(completed.pageId!==doc.activeId)return;
  const xs=completed.points.map(q=>q[0]),ys=completed.points.map(q=>q[1]);
  const span=Math.max(Math.max(...xs)-Math.min(...xs),Math.max(...ys)-Math.min(...ys));
  if(completed.points.length>=3&&span>4){applyLasso(completed.points,completed.additive);selectionLasso=selectionEmpty()?null:completed.points.map(q=>[q[0],q[1]]);}
  else{const hit=strokeAt(completed.points[0][0],completed.points[0][1]);if(hit){if(!completed.additive)selection={strokes:new Set(),blocks:new Set()};selection.strokes.add(hit);selectionLasso=null;}}
  renderSelection();return;
 }
 if(completed.type==='marquee'){
  marqueeEl.hidden=true;
  const r={x0:Math.min(completed.start[0],completed.last[0]),y0:Math.min(completed.start[1],completed.last[1]),x1:Math.max(completed.start[0],completed.last[0]),y1:Math.max(completed.start[1],completed.last[1])};
  if(r.x1-r.x0>3||r.y1-r.y0>3)applyMarquee(r,completed.additive);
  return;
 }
 if(completed.changed){const p=pageById(completed.pageId);if(p)commit(completed.before,p);if(completed.type==='ink'){if(completed.needsRedraw)redraw();else{updateHint();renderSelection();}}else{renderBlocks();redraw();}}
 if(completed.type==='ink')perf.finish=Math.round(performance.now()-t0);
}
sheet.addEventListener('pointerleave',()=>{eraserCursor.hidden=true;});
for(const event of ['pointerup','pointercancel','lostpointercapture'])sheet.addEventListener(event,e=>{if(gesture&&e.pointerId===gesture.id)finish();});
// iPad Safari: pointer events alone are not enough. A stylus touch that is not
// default-prevented can be taken over by page scrolling or Scribble, and the
// stroke is cancelled. Touch listeners are non-passive so preventDefault works.
const stylusTouch=e=>[...(e.changedTouches||[])].some(t=>t.touchType==='stylus');
// iPad / iPhone: the OS tells stylus and finger apart, so fingers may scroll the page even in
// pen mode (stylus touches are default-prevented above). Other platforms keep touch-action:none.
const isIOS=/iPad|iPhone|iPod/.test(navigator.userAgent)||(navigator.platform==='MacIntel'&&navigator.maxTouchPoints>1);
if(isIOS)document.body.classList.add('ios');
const activeGesture=()=>gesture&&['ink','lasso','marquee','drag','move','resize'].includes(gesture.type);
sheet.addEventListener('touchstart',e=>{
 if(!ready||document.body.classList.contains('reading'))return;
 const inkTool=tool==='pen'||tool==='eraser'||tool==='select'||(tool==='text'&&$('auto-pen').checked);
 if((stylusTouch(e)&&inkTool)||activeGesture())e.preventDefault();
},{passive:false});
sheet.addEventListener('touchmove',e=>{if(activeGesture())e.preventDefault();},{passive:false});
for(const event of ['touchend','touchcancel'])sheet.addEventListener(event,e=>{
 if(gesture&&stylusTouch(e)&&e.touches.length===0){const id=gesture.id;setTimeout(()=>{if(gesture&&gesture.id===id)finish();},80);}
});
window.addEventListener('blur',finish);
document.addEventListener('visibilitychange',()=>{if(document.hidden){finish();save();}});
window.addEventListener('beforeunload',e=>{finish();if(dirty||saving){e.preventDefault();e.returnValue='';}});
sheet.addEventListener('click',e=>{
 if(!ready||tool!=='text'||performance.now()-lastInkEnd<500)return;
 const t=e.target;
 if(t!==sheet&&t!==canvas&&t!==blocksLayer&&t!==$('empty-hint')&&!$('empty-hint').contains(t)){return;}
 const [x,y]=coordinates(e);createTextBlock(x,y);
});
// ---- undo / redo ----
function undo(redo=false) {
 if(document.body.classList.contains('reading'))return;
 finish();const h=historyFor(doc.activeId),from=redo?h.redo:h.undo,to=redo?h.undo:h.redo;if(!from.length)return;
 if(document.activeElement&&sheet.contains(document.activeElement))document.activeElement.blur();
 const p=page();to.push(snapshot(p));restore(p,from.pop());editing=null;selection={strokes:new Set(),blocks:new Set()};selectionLasso=null;
 if(activeBlock&&!blockOf(activeBlock,p))activeBlock=null;
 renderPage();changed();syncHistory();
}
$('undo').onclick=()=>undo();$('redo').onclick=()=>undo(true);
document.addEventListener('keydown',e=>{
 if(!ready||e.isComposing)return;
 if(document.body.classList.contains('reading')){
  if(((e.ctrlKey||e.metaKey)&&['z','y'].includes(e.key.toLowerCase()))||['Delete','Backspace'].includes(e.key))e.preventDefault();
  return;
 }
 const typing=['INPUT','TEXTAREA'].includes(e.target.tagName)||(e.target instanceof Element&&e.target.isContentEditable);
 if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='z'&&!typing){e.preventDefault();undo(e.shiftKey);return;}
 if(typing)return;
 if(tool==='select'){
  const step=e.shiftKey?10:1,arrows={ArrowLeft:[-step,0],ArrowRight:[step,0],ArrowUp:[0,-step],ArrowDown:[0,step]};
  if(arrows[e.key]){e.preventDefault();nudgeSelection(...arrows[e.key]);return;}
  if((e.key==='Delete'||e.key==='Backspace')&&!selectionEmpty()){e.preventDefault();deleteSelection();return;}
  if(e.key==='Escape'){clearSelection();return;}
  if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='a'){e.preventDefault();const p=page(),L=editableLayer(true);selection={strokes:new Set(p.strokes.filter(s=>L&&s.layer===L.id)),blocks:new Set(p.blocks.map(b=>b.id))};selectionLasso=null;renderSelection();return;}
 }
 if((e.key==='Delete'||e.key==='Backspace')&&activeBlock){e.preventDefault();removeBlock(activeBlock);}
 if(e.key==='Escape'&&activeBlock)setActive(null);
});
// ---- text formatting ----
function currentEditor() {
 if(document.body.classList.contains('reading'))return null;
 const el=document.activeElement;
 if(el instanceof Element&&el.classList.contains('editor')&&sheet.contains(el))return el;
 if(activeBlock){const ed=blocksLayer.querySelector('[data-id="'+activeBlock+'"] .editor');if(ed){ed.focus();return ed;}}
 message('先に文字の入力欄をクリックしてください。文字をドラッグで選ぶと、その部分だけに書式が付きます。');return null;
}
function ensureSelection(ed) {
 const sel=getSelection();
 if(!sel.rangeCount||!ed.contains(sel.anchorNode)||sel.isCollapsed){const r=document.createRange();r.selectNodeContents(ed);sel.removeAllRanges();sel.addRange(r);}
}
function notifyInput(ed){ed.dispatchEvent(new Event('input',{bubbles:true}));}
function applyBold(){const ed=currentEditor();if(!ed)return;ensureSelection(ed);document.execCommand('styleWithCSS',false,'false');document.execCommand('bold');}
function applyColor(color){const ed=currentEditor();if(!ed)return;ensureSelection(ed);document.execCommand('styleWithCSS',false,'false');document.execCommand('foreColor',false,color);}
function applySize(px) {
 const ed=currentEditor();if(!ed)return;ensureSelection(ed);
 document.execCommand('styleWithCSS',false,'false');document.execCommand('fontSize',false,'7');
 const spans=[];
 for(const f of ed.querySelectorAll('font[size="7"]')){const span=document.createElement('span');span.style.fontSize=clamp(Math.round(px),MIN_FONT,MAX_FONT)+'px';while(f.firstChild)span.append(f.firstChild);f.replaceWith(span);spans.push(span);}
 if(spans.length){const r=document.createRange();r.setStartBefore(spans[0]);r.setEndAfter(spans.at(-1));const sel=getSelection();sel.removeAllRanges();sel.addRange(r);}
 notifyInput(ed);
}
function selectionFontSize(ed) {
 const sel=getSelection();let node=sel.rangeCount?sel.anchorNode:ed;if(node&&node.nodeType===3)node=node.parentElement;
 if(!node||!ed.contains(node))node=ed;
 return Math.round(parseFloat(getComputedStyle(node).fontSize))||15;
}
function insertRule() {
 const ed=currentEditor();if(!ed)return;
 const sel=getSelection();if(!sel.rangeCount||!ed.contains(sel.anchorNode)){const r=document.createRange();r.selectNodeContents(ed);r.collapse(false);sel.removeAllRanges();sel.addRange(r);}
 document.execCommand('insertHorizontalRule');
 if(!(ed.lastChild instanceof HTMLBRElement)&&ed.lastChild?.tagName==='HR')ed.append(document.createElement('br'));
 notifyInput(ed);
}
for(const el of document.querySelectorAll('.text-tools button'))el.addEventListener('mousedown',e=>e.preventDefault());
$('fmt-bold').onclick=applyBold;
$('fmt-hr').onclick=insertRule;
$('fmt-smaller').onclick=()=>{const ed=currentEditor();if(ed)applySize(selectionFontSize(ed)-2);};
$('fmt-larger').onclick=()=>{const ed=currentEditor();if(ed)applySize(selectionFontSize(ed)+2);};
document.querySelectorAll('.fmt-size').forEach(b=>b.onclick=()=>applySize(Number(b.dataset.size)));
document.querySelectorAll('.fmt-color').forEach(b=>b.onclick=()=>applyColor(b.dataset.color));
$('fmt-color-clear').onclick=()=>applyColor(DEFAULT_TEXT_COLOR);
$('fmt-color-pick').addEventListener('mousedown',()=>{const ed=document.activeElement;if(ed instanceof Element&&ed.classList.contains('editor'))activeBlock=ed.closest('.block')?.dataset.id||activeBlock;});
$('fmt-color-pick').oninput=e=>{const hex=toHex(e.target.value);if(hex)applyColor(hex);};
// ---- layer panel ----
const layerPanel=$('layer-panel'),layerList=$('layer-list');
let layerDrag=null,opacityBefore=null,layerDeleteArmed=-1e9,panelDrag=null;
function iconButton(cls,name,label,handler) {
 const b=document.createElement('button');b.type='button';b.className=cls;b.append(icon(name));b.title=label;b.setAttribute('aria-label',label);b.draggable=false;
 b.onclick=e=>{e.stopPropagation();handler();};return b;
}
function renderLayers() {
 if(!doc)return;const p=page();ensureLayers(p);const active=activeLayerOf(p);
 layerList.replaceChildren();
 for(const L of [...p.layers].reverse()){
  const row=document.createElement('div');row.className='layer-row'+(L.id===active.id?' active':'')+(L.visible?'':' hidden-layer')+(L.locked?' locked':'');
  row.dataset.layerId=L.id;row.draggable=true;row.setAttribute('role','option');row.setAttribute('aria-selected',String(L.id===active.id));
  row.append(iconButton('layer-eye',L.visible?'eye':'eye-off',L.visible?'「'+L.name+'」を非表示にする':'「'+L.name+'」を表示する',()=>layerChange(L.id,{visible:!L.visible})));
  row.append(iconButton('layer-lock',L.locked?'lock':'unlock',L.locked?'「'+L.name+'」のロックを解除':'「'+L.name+'」をロック',()=>layerChange(L.id,{locked:!L.locked})));
  const name=document.createElement('span');name.className='layer-name';name.textContent=L.name;name.title=L.name;
  const op=document.createElement('span');op.className='layer-op';op.textContent=Math.round(L.opacity*100)+'%';
  row.append(name,op);
  row.onclick=()=>{if(p.activeLayer!==L.id){p.activeLayer=L.id;clearSelection();changed();renderLayers();}};
  row.ondblclick=()=>startLayerRename(L.id);
  layerList.append(row);
 }
 $('layer-count').textContent=p.layers.length+' / '+MAX_LAYERS;
 $('layer-add').disabled=!ready||p.layers.length>=MAX_LAYERS;$('layer-delete').disabled=!ready||p.layers.length<2;$('layer-rename').disabled=!ready;
 const pct=Math.round(active.opacity*100);$('layer-opacity').value=pct;$('layer-opacity-value').value=pct+'%';
}
function layerChange(id,patch) {
 const p=page(),before=snapshot(p);if(!updateLayer(p,id,patch))return;
 if(patch.visible===false||patch.locked===true)clearSelection();
 commit(before);redraw();renderLayers();
}
function startLayerRename(id) {
 const p=page(),L=p.layers.find(l=>l.id===id);if(!L)return;
 const row=layerList.querySelector('[data-layer-id="'+id+'"]'),name=row?.querySelector('.layer-name');if(!name)return;
 const input=document.createElement('input');input.type='text';input.maxLength=40;input.value=L.name;input.setAttribute('aria-label','レイヤーの名前');
 row.draggable=false;name.replaceWith(input);input.focus();input.select();
 let done=false;
 const finishRename=()=>{if(done)return;done=true;const next=input.value.trim()||'名称未設定';if(next!==L.name){const before=snapshot(p);updateLayer(p,id,{name:next});commit(before);}renderLayers();};
 input.addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();finishRename();}else if(e.key==='Escape'){done=true;renderLayers();}e.stopPropagation();});
 input.addEventListener('blur',finishRename);input.addEventListener('click',e=>e.stopPropagation());input.addEventListener('dblclick',e=>e.stopPropagation());
}
$('layer-add').onclick=()=>{const p=page(),before=snapshot(p);if(!addLayer(p)){message('レイヤーは1ページに'+MAX_LAYERS+'枚までです。');return;}clearSelection();commit(before);renderLayers();};
$('layer-rename').onclick=()=>startLayerRename(page().activeLayer);
$('layer-delete').onclick=()=>{
 const btn=$('layer-delete'),now=performance.now();
 if(now-layerDeleteArmed<4000){
  layerDeleteArmed=0;$('layer-delete-label').textContent='削除';btn.classList.remove('confirm');
  const p=page(),L=activeLayerOf(p),before=snapshot(p);
  if(removeLayer(p,L.id)){clearSelection();commit(before);redraw();renderLayers();message('レイヤー「'+L.name+'」を削除しました。「↶」で戻せます。');}
  return;
 }
 layerDeleteArmed=now;const n=page().strokes.filter(s=>s.layer===page().activeLayer).length;
 $('layer-delete-label').textContent='もう一度押すと削除'+(n?'（線 '+n+' 本）':'');btn.classList.add('confirm');
 setTimeout(()=>{if(performance.now()-layerDeleteArmed>=3900){layerDeleteArmed=0;$('layer-delete-label').textContent='削除';btn.classList.remove('confirm');}},4000);
};
$('layer-opacity').oninput=e=>{
 const p=page();if(!opacityBefore)opacityBefore=snapshot(p);
 updateLayer(p,p.activeLayer,{opacity:clamp(Number(e.target.value)/100,0,1)});redraw();
 $('layer-opacity-value').value=e.target.value+'%';const row=layerList.querySelector('.layer-row.active .layer-op');if(row)row.textContent=e.target.value+'%';
};
$('layer-opacity').onchange=()=>{if(opacityBefore){commit(opacityBefore);opacityBefore=null;}renderLayers();};
// reorder rows by drag (rows are listed top-first; layers are stored bottom-first)
layerList.addEventListener('dragstart',e=>{const row=e.target instanceof Element?e.target.closest('.layer-row'):null;if(!row){e.preventDefault();return;}layerDrag=row.dataset.layerId;row.classList.add('dragging');e.dataTransfer.effectAllowed='move';try{e.dataTransfer.setData('text/plain','layer');}catch{}});
layerList.addEventListener('dragend',()=>{layerDrag=null;for(const el of layerList.querySelectorAll('.dragging,.drop-before,.drop-after'))el.classList.remove('dragging','drop-before','drop-after');});
function layerDropTarget(e){const row=e.target instanceof Element?e.target.closest('.layer-row'):null;if(!row||!layerDrag||row.dataset.layerId===layerDrag)return null;const r=row.getBoundingClientRect();return {row,before:e.clientY<r.top+r.height/2};}
layerList.addEventListener('dragover',e=>{if(!layerDrag)return;const t=layerDropTarget(e);for(const el of layerList.querySelectorAll('.drop-before,.drop-after'))el.classList.remove('drop-before','drop-after');if(!t)return;e.preventDefault();e.dataTransfer.dropEffect='move';t.row.classList.add(t.before?'drop-before':'drop-after');});
layerList.addEventListener('drop',e=>{
 if(!layerDrag)return;e.preventDefault();const t=layerDropTarget(e),id=layerDrag;layerDrag=null;if(!t)return;
 const p=page(),before=snapshot(p),display=[...p.layers].reverse().filter(l=>l.id!==id),moving=p.layers.find(l=>l.id===id);
 let i=display.findIndex(l=>l.id===t.row.dataset.layerId);if(!t.before)i++;display.splice(i,0,moving);
 p.layers=display.reverse();commit(before);redraw();renderLayers();
});
// panel: collapse and drag anywhere on screen; position is remembered per browser
function savePanelState(){try{localStorage.setItem('yohaku-layer-panel',JSON.stringify({left:layerPanel.style.left,top:layerPanel.style.top,collapsed:layerPanel.classList.contains('collapsed')}));}catch{}}
function placePanel(x,y){x=clamp(x,0,Math.max(0,innerWidth-layerPanel.offsetWidth));y=clamp(y,0,Math.max(0,innerHeight-44));layerPanel.style.left=Math.round(x)+'px';layerPanel.style.top=Math.round(y)+'px';layerPanel.style.right='auto';}
let panelPlaced=false;
try{const st=JSON.parse(localStorage.getItem('yohaku-layer-panel')||'null');if(st){if(st.left&&st.top){placePanel(parseFloat(st.left),parseFloat(st.top));panelPlaced=true;}if(st.collapsed)layerPanel.classList.add('collapsed');}}catch{}
// First run on a wide screen: put the panel beside the page, below the toolbar, so it never
// covers the tool buttons. The user can drag it anywhere afterwards.
function placePanelDefault(){if(panelPlaced||innerWidth<=1180||layerPanel.hidden)return;const r=paper.getBoundingClientRect();placePanel(innerWidth-layerPanel.offsetWidth-24,Math.max(80,r.top+12));panelPlaced=true;}
$('layer-collapse').onclick=()=>{const c=layerPanel.classList.toggle('collapsed');$('layer-collapse').replaceChildren(icon(c?'chevron-down':'chevron-up'));$('layer-collapse').setAttribute('aria-expanded',String(!c));$('layer-collapse').setAttribute('aria-label',c?'レイヤー一覧を開く':'レイヤー一覧を折りたたむ');savePanelState();};
if(layerPanel.classList.contains('collapsed')){$('layer-collapse').replaceChildren(icon('chevron-down'));$('layer-collapse').setAttribute('aria-expanded','false');}
$('layer-head').addEventListener('pointerdown',e=>{
 if(e.target instanceof Element&&e.target.closest('button'))return;if(innerWidth<=1180)return;
 e.preventDefault();const r=layerPanel.getBoundingClientRect();panelDrag={id:e.pointerId,dx:e.clientX-r.left,dy:e.clientY-r.top};
 try{$('layer-head').setPointerCapture(e.pointerId);}catch{}
});
$('layer-head').addEventListener('pointermove',e=>{if(!panelDrag||e.pointerId!==panelDrag.id)return;placePanel(e.clientX-panelDrag.dx,e.clientY-panelDrag.dy);});
for(const ev of ['pointerup','pointercancel'])$('layer-head').addEventListener(ev,e=>{if(panelDrag&&e.pointerId===panelDrag.id){panelDrag=null;savePanelState();}});
window.addEventListener('resize',()=>{if(layerPanel.style.left)placePanel(parseFloat(layerPanel.style.left),parseFloat(layerPanel.style.top));});
// ---- tools ----
const hints={text:'クリックした場所に文字を入力できます。ペンで触れると手書きになります',pen:'ペンやマウスでドラッグして書きます。文字や画像の上にも書けます',
 part:'なぞった部分だけ消します。「大きさ」で消しゴムの太さを変えられます',whole:'触れた線を一本ごと消します。「大きさ」で消しゴムの太さを変えられます',
 rect:'四角で囲んで選択（触れた線はまるごと）。文字や画像はクリックで選択。ドラッグや矢印キーで移動できます',
 lasso:'ペンやマウスで自由に囲むと、囲んだ部分だけが切り出されて選ばれます（線の上から囲み始めても大丈夫）。囲み終わったら枠の中をドラッグして移動'};
hints.select=hints.rect;
function chooseTool(value) {
 finish();tool=value;
 for(const name of ['text','pen','eraser','select']){$('tool-'+name).classList.toggle('selected',tool===name);$('tool-'+name).setAttribute('aria-pressed',String(tool===name));}
 $('eraser-options').hidden=tool!=='eraser';$('select-options').hidden=tool!=='select';
 sheet.classList.toggle('ink',tool==='pen'||tool==='eraser');sheet.classList.toggle('erase',tool==='eraser');sheet.classList.toggle('select',tool==='select');
 if(tool!=='eraser'&&tool!=='pen')eraserCursor.hidden=true;
 if(tool!=='text'){setActive(null);if(document.activeElement&&sheet.contains(document.activeElement))document.activeElement.blur();}
 $('tool-hint').textContent=tool==='eraser'?hints[eraserMode]:hints[tool];
 clearSelection();updateToolPresentation();
}
function chooseSelectMode(value) {
 selectMode=value;hints.select=hints[value];
 for(const name of ['rect','lasso']){$('select-'+name).classList.toggle('selected',selectMode===name);$('select-'+name).setAttribute('aria-pressed',String(selectMode===name));}
 chooseTool('select');
}
$('select-rect').onclick=()=>chooseSelectMode('rect');$('select-lasso').onclick=()=>chooseSelectMode('lasso');
function chooseEraser(value) {
 eraserMode=value;
 for(const name of ['part','whole']){$('eraser-'+name).classList.toggle('selected',eraserMode===name);$('eraser-'+name).setAttribute('aria-pressed',String(eraserMode===name));}
 chooseTool('eraser');
}
$('tool-text').onclick=()=>chooseTool('text');$('tool-pen').onclick=()=>chooseTool('pen');$('tool-eraser').onclick=()=>chooseTool('eraser');$('tool-select').onclick=()=>chooseTool('select');
$('eraser-size').oninput=e=>{eraserSize=Number(e.target.value);$('eraser-size-value').value=eraserSize;};
$('eraser-part').onclick=()=>chooseEraser('part');$('eraser-whole').onclick=()=>chooseEraser('whole');
function setColor(value) {
 color=value;$('color').value=value;chooseTool('pen');
 document.querySelectorAll('.swatch').forEach(b=>{b.classList.toggle('selected',b.dataset.color===value);b.setAttribute('aria-pressed',String(b.dataset.color===value));});
}
document.querySelectorAll('.swatch').forEach(b=>b.onclick=()=>setColor(b.dataset.color));
$('color').oninput=e=>setColor(e.target.value);
$('width').oninput=e=>{width=Number(e.target.value);$('width-value').value=width;};
$('page-title').oninput=e=>{page().title=e.target.value;breadcrumb();changed();renderPages();};
function growAndReveal() {
 finish();const p=page(),before=snapshot(p),prev=p.height;
 if(!growPage(p,p.height+400)){message('このページは上限（'+MAX_HEIGHT+'）まで広がっています。左の「ページを追加」で次のページを作ってください。');return;}
 commit(before);
 // show the new space: scroll so that the old bottom edge sits in view
 const rect=sheet.getBoundingClientRect(),target=rect.top+prev*scale-Math.max(120,innerHeight*.45);
 window.scrollBy({top:target,behavior:'smooth'});
 message('ページを下に広げました（高さ '+p.height+' / 最大 '+MAX_HEIGHT+'）。');
}
$('grow-page').onclick=growAndReveal;
$('add-page').onclick=()=>{
 if(doc.pages.length>=500){message('試作品では500ページまで作れます。');return;}
 const sec=currentSection();showForm({kind:'new-page'},'新しいページ（'+sec.name+'）','','作成');
};
function download(content,name,type='application/json') {
 const url=URL.createObjectURL(new Blob([content],{type})),a=document.createElement('a');
 a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),30000);
}
$('export').onclick=()=>{finish();download(JSON.stringify(doc,null,2),'余白ノート_'+new Date().toISOString().replaceAll(':','-')+'.json');};
$('export-svg').onclick=()=>{
 finish();const p=page();
 const svg=pageToSvg(p);
 const hidden=p.layers.filter(L=>!L.visible).length;
 download(svg,(p.title||'名称未設定').replace(/[\\/:*?"<>|]/g,'_').slice(0,80)+'.svg','image/svg+xml');
 message('SVGを書き出しました。Illustrator で開くと、レイヤーごとのグループとして編集できます。'+(hidden?'非表示のレイヤー'+hidden+'枚は含めていません。':''));
};
$('import').onclick=()=>{$('import-file').value='';$('import-file').click();};
$('import-file').onchange=async e=>{
 const file=e.target.files[0];if(!file)return;
 try{
  if(file.size>200*1024*1024)throw new Error('200MB以下のバックアップを選んでください。');
  const incoming=upgradeNotebook(JSON.parse(await file.text()));finish();
  const draft=structuredClone(doc),r=mergeNotebook(draft,incoming);
  doc=validateBackup(draft);histories.clear();dirtyAll=true;selectedSectionId=null;showPage();changed();
  message('取り込みました：新しいページ '+r.added+'、更新 '+r.updated+'、変更なし '+r.unchanged+(r.skipped?'、ゴミ箱にあるため戻さなかったページ '+r.skipped:'')+'。同じページは日時の新しい方を残しています。');
 }catch(error){message('読み込めませんでした。元のメモは変更していません。 '+error.message);}
};
// ---- cloud sync (see sync.mjs) ----
let syncEngine=null,syncTransport=null,applyingRemote=false,syncUser=null,syncObserved=null;
const $sync=id=>$('sync-'+id);
function syncSignature(){return JSON.stringify([doc.notebooks||[],doc.sections||[],doc.pages.map(p=>p.id)]);}
function syncSnapshot(){syncObserved={pages:new Set(doc.pages.map(p=>p.id)),trash:new Set((doc.trash||[]).map(t=>t.id)),sig:syncSignature()};}
// After any local change: pages that appeared/disappeared, trash entries that appeared/disappeared,
// and layout changes are queued for upload. The changed page itself is marked by changed().
function syncObserve() {
 if(!syncEngine||!syncObserved)return;
 const pages=new Set(doc.pages.map(p=>p.id)),trash=new Set((doc.trash||[]).map(t=>t.id));
 for(const id of pages)if(!syncObserved.pages.has(id))syncEngine.markPage(id);
 for(const id of syncObserved.pages)if(!pages.has(id))syncEngine.removePage(id);
 for(const id of trash)if(!syncObserved.trash.has(id))syncEngine.markTrash(id);
 for(const id of syncObserved.trash)if(!trash.has(id))syncEngine.removeTrash(id);
 const sig=syncSignature();
 if(sig!==syncObserved.sig){doc.metaUpdatedAt=Date.now();syncEngine.markNotebook();}
 syncObserved={pages,trash,sig};
}
function syncSetStatus(state,detail,error) {
 const el=$('sync-status'),text=$('sync-status-text'),badge=$('sync-badge');
 const map={off:['同期オフ','off','オフ',''],connecting:['接続中…','warn','接続中','warn'],online:['同期済み','','オン','on'],sending:['送信中 '+(detail||''),'warn','送信中','warn'],offline:['オフライン（後で送信）','warn','オフライン','warn'],error:['同期エラー','err','エラー','err']};
 const [label,cls,badgeText,badgeCls]=map[state]||map.off;
 el.hidden=state==='off';el.className='sync-status '+cls;text.textContent=label;badge.textContent=badgeText;badge.className='sync-badge '+badgeCls;
 if(state==='error'&&error){$sync('detail').textContent='エラー: '+(error.code||error.message||error);console.warn('sync',error);}
 else if(state==='online')$sync('detail').textContent='この端末とクラウドは同じ状態です。'+(detail&&detail.lastWriteMs?'（最後の送信 '+(detail.lastWriteMs/1000).toFixed(1)+' 秒）':'');
 else if(state==='offline')$sync('detail').textContent='つながったときに自動で送ります（未送信 '+(detail||0)+'）。';
}
function syncMessage(text){const el=$sync('message');el.textContent=text;el.hidden=!text;}
function validateRemotePage(pg){try{validateBackup({version:2,pages:[pg],activeId:pg.id});return true;}catch(e){console.warn('remote page rejected',e);return false;}}
function validateRemoteTrash(entry){try{const d=newPage('x');validateBackup({version:2,pages:[d],activeId:d.id,trash:[entry]});return true;}catch(e){console.warn('remote trash rejected',e);return false;}}
function applyRemotePage(id,pg) {
 applyingRemote=true;
 try{
  const i=doc.pages.findIndex(x=>x.id===id);
  if(!pg){
   if(i<0)return;doc.pages.splice(i,1);histories.delete(id);
   if(!doc.pages.length)doc.pages.push(newPage('はじめのページ'));
   if(doc.activeId===id)doc.activeId=doc.pages[Math.min(i,doc.pages.length-1)].id;
  } else {
   ensureLayers(pg);if(i>=0)doc.pages[i]=pg;else doc.pages.push(pg);histories.delete(id);dirtyPages.add(id);
  }
  ensureStructure(doc);revision++;dirty=true;
  if(!pg||id===doc.activeId)showPage();else renderPages();
  save();
 }finally{applyingRemote=false;syncSnapshot();}
}
function applyRemoteTrash(id,entry) {
 applyingRemote=true;
 try{
  doc.trash=(doc.trash||[]).filter(t=>t.id!==id);
  if(entry){
   doc.trash.push(entry);dirtyTrash.add(id);
   const ids=new Set(entry.pages.map(pg=>pg.id));
   if(doc.pages.some(pg=>ids.has(pg.id))){doc.pages=doc.pages.filter(pg=>!ids.has(pg.id));if(!doc.pages.length)doc.pages.push(newPage('はじめのページ'));if(!doc.pages.some(pg=>pg.id===doc.activeId))doc.activeId=doc.pages[0].id;}
  }
  ensureStructure(doc);revision++;dirty=true;showPage();save();
 }finally{applyingRemote=false;syncSnapshot();}
}
function applyRemoteNotebook(meta) {
 applyingRemote=true;
 try{
  const order=Array.isArray(meta.order)?meta.order:[],byId=new Map(doc.pages.map(pg=>[pg.id,pg]));
  const ordered=order.map(id=>byId.get(id)).filter(Boolean);for(const pg of doc.pages)if(!order.includes(pg.id))ordered.push(pg);
  doc.pages=ordered;
  // notebooks/sections: remote wins per id, local-only ones are kept (they may still be waiting for upload)
  const hex=/^#[0-9a-f]{6}$/i;
  if(Array.isArray(meta.notebooks)){const remote=meta.notebooks.filter(n=>n&&typeof n.id==='string'&&typeof n.name==='string'&&n.name.trim()&&hex.test(n.color||''));const ids=new Set(remote.map(n=>n.id));doc.notebooks=[...remote.map(n=>({id:n.id,name:n.name.slice(0,60),color:n.color.toLowerCase()})),...(doc.notebooks||[]).filter(n=>!ids.has(n.id))];}
  if(Array.isArray(meta.sections)){const remote=meta.sections.filter(x=>x&&typeof x.id==='string'&&typeof x.notebookId==='string'&&typeof x.name==='string'&&x.name.trim()&&hex.test(x.color||''));const ids=new Set(remote.map(x=>x.id));doc.sections=[...remote.map(x=>({id:x.id,notebookId:x.notebookId,name:x.name.slice(0,60),color:x.color.toLowerCase()})),...(doc.sections||[]).filter(x=>!ids.has(x.id))];}
  ensureStructure(doc);doc.metaUpdatedAt=meta.updatedAt||Date.now();revision++;dirty=true;breadcrumb();renderPages();save();
 }finally{applyingRemote=false;syncSnapshot();}
}
async function syncBoot() {
 const useFake=(()=>{try{return localStorage.getItem('yohaku-sync-fake')==='1';}catch{return false;}})();
 const wanted=(()=>{try{return localStorage.getItem('yohaku-sync')==='on';}catch{return false;}})();
 if(!wanted&&!useFake){syncSetStatus('off');return;}
 await syncConnect(useFake);
}
async function syncConnect(useFake) {
 if(syncTransport)return true;
 syncSetStatus('connecting');
 try{syncTransport=useFake?createFakeTransport():await createFirebaseTransport();}
 catch(e){syncTransport=null;syncSetStatus(navigator.onLine?'error':'offline',0,e);syncMessage('同期の準備ができませんでした。インターネットに接続して、もう一度お試しください。');return false;}
 syncEngine=createSyncEngine(syncTransport,{
  getDoc:()=>doc,setStatus:syncSetStatus,applyPage:applyRemotePage,applyTrash:applyRemoteTrash,applyNotebook:applyRemoteNotebook,
  isBusy:()=>!!gesture||!!editing||!ready,validatePage:validateRemotePage,validateTrash:validateRemoteTrash
 });
 syncTransport.onAuth(user=>{
  syncUser=user;
  $sync('signed-out').hidden=!!user;$sync('signed-in').hidden=!user;
  if(user){
   $sync('account').textContent=user.email+' としてログイン中';
   try{localStorage.setItem('yohaku-sync','on');}catch{}
   syncSnapshot();syncEngine.start(user.uid);
  } else {
   syncEngine.stop();syncSetStatus('off');
  }
 });
 window.addEventListener('online',()=>syncEngine?.retry());
 return true;
}
$sync('form').onsubmit=async e=>{
 e.preventDefault();syncMessage('');
 if(!(await syncConnect(false)))return;
 try{await syncTransport.signIn($sync('email').value.trim(),$sync('password').value);syncMessage('');}
 catch(err){syncMessage(describeAuthError(err));}
};
$sync('signup').onclick=async()=>{
 syncMessage('');if(!$sync('email').value.trim()||$sync('password').value.length<6){syncMessage('メールアドレスと、6文字以上のパスワードを入れてください。');return;}
 if(!(await syncConnect(false)))return;
 try{await syncTransport.signUp($sync('email').value.trim(),$sync('password').value);syncMessage('登録しました。もう一方の端末でも、同じメールアドレスとパスワードでログインしてください。');}
 catch(err){syncMessage(describeAuthError(err));}
};
$sync('reset').onclick=async()=>{
 const email=$sync('email').value.trim();if(!email){syncMessage('先にメールアドレスを入れてください。');return;}
 if(!(await syncConnect(false)))return;
 try{await syncTransport.resetPassword(email);syncMessage('パスワード再設定のメールを送りました。届いたメールの案内に従ってください。');}catch(err){syncMessage(describeAuthError(err));}
};
$sync('logout').onclick=async()=>{
 if(syncEngine&&syncEngine.pendingCount()){syncMessage('未送信の変更があります。「同期済み」になってからログアウトしてください。');return;}
 try{localStorage.setItem('yohaku-sync','off');}catch{}
 try{await syncTransport.signOut();}catch{}
 syncMessage('ログアウトしました。この端末のメモはそのまま残ります。');
};
// Offline support + automatic update: a new version published on the server replaces the
// old one on the next open, without the user clearing site data.
function setupServiceWorker() {
 let reloading=false;const hadController=!!navigator.serviceWorker.controller; // first install must not reload or warn
 navigator.serviceWorker.addEventListener('controllerchange',()=>{
  if(reloading||!hadController||!navigator.serviceWorker.controller)return;reloading=true;
  if(dirty||saving){message('新しい版に更新しました。保存が終わったら再読み込みしてください。');return;}
  location.reload();
 });
 navigator.serviceWorker.register('./sw.js',{updateViaCache:'none'}).then(reg=>{
  reg.addEventListener('updatefound',()=>{const w=reg.installing;if(!w)return;w.addEventListener('statechange',()=>{if(w.state==='installed'&&navigator.serviceWorker.controller)message('新しい版を読み込んでいます…');});});
  document.addEventListener('visibilitychange',()=>{if(!document.hidden)reg.update().catch(()=>{});});
 }).catch(()=>message('オフライン起動の準備ができませんでした。通常の起動ファイルからは引き続き利用できます。'));
}
async function start() {
 try{
  db=await openStore();const loaded=await loadNotebook(db),saved=loaded.doc;
  if(loaded.legacy&&saved&&saved.version!==1){dirtyAll=true;dropLegacy=true;dirty=true;revision++;} // move the old single document to the split layout
  if(saved&&saved.version===1){
   const next=upgradeNotebook(saved);await migrateNotebook(db,saved,next);doc=next;
   message('以前のメモを新しい形式に変換しました。文章はページ内の入力欄に移し、手書きの位置はそのままです。変換前のデータもブラウザ内に残しています。');
  }
  else if(saved)doc=validateBackup(saved);
  else{const p=newPage('はじめのページ');doc={version:2,pages:[p],activeId:p.id};}
  let filled=ensureStructure(doc);for(const p of doc.pages)if(ensureLayers(p))filled=true;
  lastSaved={pages:new Set(doc.pages.map(pg=>pg.id)),trash:new Set((doc.trash||[]).map(t=>t.id))};
  if(filled)dirtyAll=true;
  ready=true;document.querySelectorAll('button,input,textarea,select').forEach(el=>el.disabled=false);
  lastPaperWidth=paper.clientWidth;showPage();chooseTool('text');
  if(filled){revision++;dirty=true;save();}
  if(saved&&saved.version!==1)setStatus('保存済み');else changed();
  if('serviceWorker' in navigator)setupServiceWorker();
  syncBoot();
 }catch(error){
  message('メモを開けませんでした。元の保存データを上書きせず停止しています。ブラウザの保存設定を確認し、再読み込みしてください。 '+error.message);
  setStatus('読み込み停止',true);
 }
}
if(navigator.locks){
 navigator.locks.request('yohaku-notebook-editor',{ifAvailable:true},async lock=>{
  if(!lock){message('別のタブで余白ノートを開いています。同時編集を防ぐため、このタブでは編集できません。先に開いたタブを閉じてから再読み込みしてください。');setStatus('別のタブで編集中');return;}
  await start();await new Promise(()=>{});
 }).catch(error=>{message('編集用のロックを取得できませんでした。再読み込みしてください。 '+error.message);});
}else {message('このブラウザは同時編集の保護に対応していません。WindowsのEdgeまたはChromeで開いてください。');setStatus('対応ブラウザで開いてください');}

// ---- presentation controls (not part of saved notebook data) ----
function updateToolPresentation(){
 document.body.dataset.tool=tool;
 if($('pen-settings'))$('pen-settings').hidden=tool!=='pen';
 const textTools=document.querySelector('.text-tools');if(textTools)textTools.hidden=tool!=='text';
 if($('view-pan')?.getAttribute('aria-pressed')==='true')setReading(false);
}
function setReading(reading){
 finish();if(reading&&sheet.contains(document.activeElement))document.activeElement.blur();
 document.body.classList.toggle('reading',reading);
 sheet.inert=reading;
 if(reading){clearSelection();setActive(null);}
 document.querySelector('.toolbar-context').inert=reading;
 document.querySelector('.history').inert=reading;
 $('view-pan').setAttribute('aria-pressed',String(reading));
 $('view-pan').replaceChildren(icon(reading?'pen':'hand'),reading?'編集に戻る':'閲覧');
 $('view-pan').title=reading?'編集を再開します':'書き込まずに、指でページをスクロールできます';
 eraserCursor.hidden=true;
}
function initializePresentation(){
 const toolbar=document.querySelector('.toolbar');
 const primary=document.createElement('div');primary.className='toolbar-primary';
 const contextual=document.createElement('div');contextual.className='toolbar-context';contextual.setAttribute('aria-label','選択中の道具の設定');
 const penSettings=document.createElement('div');penSettings.id='pen-settings';penSettings.className='pen-settings';
 const modes=document.querySelector('.modes'),images=$('add-image').parentElement,historyEl=document.querySelector('.history');
 const textTools=document.querySelector('.text-tools'),colors=document.querySelector('.colors'),weight=$('width').parentElement;
 const pressure=$('pressure').parentElement,auto=$('auto-pen').parentElement;
 penSettings.append(colors,weight,pressure,auto);
 primary.append(modes,images,historyEl);
 contextual.append(textTools,penSettings,$('eraser-options'),$('select-options'));
 toolbar.replaceChildren(primary,contextual);
 updateToolPresentation();
 const sidebar=document.querySelector('.sidebar'),navToggle=$('nav-toggle'),compact=matchMedia('(max-width:1180px)');
 let desktopHidden=false;
 function navOpen(){return compact.matches?document.body.classList.contains('nav-open'):!desktopHidden;}
 function syncNavigation(){
  const opened=navOpen();navToggle.setAttribute('aria-expanded',String(opened));
  sidebar.inert=!opened;document.querySelector('main').inert=compact.matches&&opened;$('nav-backdrop').hidden=!(compact.matches&&opened);
  document.body.classList.toggle('nav-collapsed',!compact.matches&&desktopHidden);
  if(compact.matches&&opened){sidebar.setAttribute('role','dialog');sidebar.setAttribute('aria-modal','true');}
  else {sidebar.removeAttribute('role');sidebar.removeAttribute('aria-modal');}
 }
 function setNav(opened,focus=false){
  if(compact.matches)document.body.classList.toggle('nav-open',opened);else desktopHidden=!opened;
  syncNavigation();if(focus)(opened?$('nav-close'):navToggle).focus({preventScroll:true});
 }
 navToggle.onclick=()=>setNav(!navOpen(),true);
 $('nav-close').onclick=()=>setNav(false,true);
 $('nav-backdrop').onclick=()=>setNav(false,true);
 compact.addEventListener('change',()=>{document.body.classList.remove('nav-open');syncNavigation();});
 // Close after selecting a page, but leave the category form and menus usable.
 $('pages').addEventListener('click',e=>{
  if(compact.matches&&e.target.closest('.page-button'))setNav(false,true);
 });
 document.addEventListener('keydown',e=>{
  if(e.key==='Escape'){
   if(!layerPanel.hidden){setLayers(false);$('layers-toggle').focus();e.preventDefault();return;}
   if(compact.matches&&navOpen()){setNav(false,true);e.preventDefault();}
  }
  if(e.key==='Tab'&&compact.matches&&navOpen()){
   const focusable=[...sidebar.querySelectorAll('button,input,summary,[tabindex="0"]')].filter(el=>!el.disabled&&el.getClientRects().length);
   const first=focusable[0],last=focusable.at(-1);
   if(e.shiftKey&&document.activeElement===first){last?.focus();e.preventDefault();}
   else if(!e.shiftKey&&document.activeElement===last){first?.focus();e.preventDefault();}
  }
 });
 syncNavigation();
 function setLayers(opened,remember=true){
  layerPanel.hidden=!opened;$('layers-toggle').setAttribute('aria-expanded',String(opened));
  if(opened)placePanelDefault();
  if(opened&&layerPanel.classList.contains('collapsed'))$('layer-collapse').click();
  if(remember)try{localStorage.setItem('yohaku-layers-open',opened?'1':'0');}catch{}
 }
 $('layers-toggle').onclick=()=>setLayers(layerPanel.hidden);
 $('layer-close').onclick=()=>{setLayers(false);$('layers-toggle').focus();};
 let layersPref=null;try{layersPref=localStorage.getItem('yohaku-layers-open');}catch{}
 setLayers(layersPref==='1'||(layersPref===null&&innerWidth>1180),false);placePanelDefault();
 const zoom=$('view-zoom');
 try{const saved=localStorage.getItem('yohaku-view-zoom');if(['fit','.75','1','1.25'].includes(saved))zoom.value=saved;}catch{}
 function applyZoom(){
  finish();paper.style.width=zoom.value==='fit'?'100%':(W*Number(zoom.value))+'px';
  $('paper-viewport').scrollLeft=0;layout();
  try{localStorage.setItem('yohaku-view-zoom',zoom.value);}catch{}
 }
 zoom.onchange=applyZoom;applyZoom();
 $('view-pan').onclick=()=>setReading(!document.body.classList.contains('reading'));
 // Ancestor capture runs before the existing drawing handlers. Native touch
 // scrolling remains enabled; no note content is changed in reading mode.
 for(const event of ['pointerdown','pointermove','pointerup','click','dblclick']){
  $('paper-viewport').addEventListener(event,e=>{
   if(document.body.classList.contains('reading'))e.stopImmediatePropagation();
  },{capture:true});
 }
}
initializePresentation();


