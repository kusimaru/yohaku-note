import { PAGE_WIDTH as W, MAX_HEIGHT, newPage, newTextBlock, inkWidth, hitStroke, erasePart, splitByPolygon, pointInPolygon, validateBackup, upgradeNotebook, categoryOf, normalizeCategories, addCategory, removeCategory, movePage, moveCategory, renameCategory, deletePage, deleteCategory, restoreTrash, purgeTrash, emptyTrash } from './model.mjs';
import { openStore, loadNotebook, saveNotebook, migrateNotebook } from './storage.mjs';
import { domToRuns, runsToDom, toHex } from './richtext.mjs';
import { pageToSvg } from './svgexport.mjs';
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
const collapsed=new Set();
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
function changed(p=page()) {
 p.updatedAt=Date.now();revision++;dirty=true;
 setStatus('保存中…');save();
}
async function save() {
 if(saving||!db||!dirty)return;
 saving=true;
 try {
  while(dirty) {
   const version=revision;
   await saveNotebook(db,doc);
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
function categoryOrder() {
 normalizeCategories(doc);
 const names=[...doc.categories];
 if(doc.pages.some(p=>!categoryOf(p)))names.push('');
 return names;
}
function openPage(id) {
 if(id===doc.activeId)return;finish();doc.activeId=id;revision++;dirty=true;showPage();save();
}
function renderPages() {
 $('pages').replaceChildren();closeMenu();
 $('trash-count').textContent=(doc.trash||[]).length;$('trash-toggle').classList.toggle('active',view==='trash');$('trash-toggle').setAttribute('aria-pressed',String(view==='trash'));
 if(view==='trash'){renderTrash();return;}
 $('list-title').textContent='ページ';$('list-tip').textContent='ドラッグで並べ替え・移動。「⋯」で名前の変更・削除';
 const names=categoryOrder();
 $('category-list').replaceChildren(...names.filter(c=>c).map(c=>{const o=document.createElement('option');o.value=c;return o;}));
 const showHeadings=names.length>1||names[0]!=='';
 for(const c of names){
  const pages=doc.pages.map((p,i)=>[p,i]).filter(([p])=>categoryOf(p)===c);
  const active=pages.some(([p])=>p.id===doc.activeId),open=!collapsed.has(c)||active;
  const group=document.createElement('div');group.className='category'+(open?'':' collapsed');group.dataset.category=c;
  if(showHeadings){
   const heading=document.createElement('button');heading.type='button';heading.className='category-heading'+(open?'':' collapsed');
   heading.dataset.category=c;heading.draggable=!!c;heading.title=c?'クリックで折りたたみ / ドラッグで並べ替え':'カテゴリのないページ';
   const label=document.createElement('span');label.className='cat-name';label.textContent=c||'未分類';heading.setAttribute('aria-expanded',String(open));
   const count=document.createElement('span');count.className='cat-count';count.textContent=pages.length;heading.append(icon('chevron-down','chev'),icon('folder','cat-icon'),label,count);
   heading.onclick=()=>{if(collapsed.has(c))collapsed.delete(c);else collapsed.add(c);renderPages();};
   const head=document.createElement('div');head.className='category-head';head.append(heading);
   if(c)head.append(menuButton({type:'category',name:c,label:c}));
   group.append(head);
  }
  const list=document.createElement('div');list.className='category-pages';list.dataset.category=c;
  if(open)for(const [p,i] of pages){
   const button=document.createElement('button');button.className='page-button'+(p.id===doc.activeId?' active':'');
   button.dataset.pageId=p.id;button.draggable=true;button.setAttribute('aria-current',p.id===doc.activeId?'page':'false');
   const name=document.createElement('span'),label=document.createElement('span');label.textContent=p.title||'名称未設定';name.append(icon('file'),label);button.append(name);
   const sub=document.createElement('small');sub.textContent=String(i+1).padStart(2,'0')+'  /  '+new Date(p.updatedAt).toLocaleDateString('ja-JP');button.append(sub);
   button.onclick=()=>openPage(p.id);
   const item=document.createElement('div');item.className='page-item';item.append(button,menuButton({type:'page',id:p.id,label:p.title||'名称未設定'}));
   list.append(item);
  }
  group.append(list);$('pages').append(group);
 }
 $('page-count').textContent=doc.pages.length;
}
// ---- item menu (rename / delete) ----
function menuButton(target) {
 const b=document.createElement('button');b.type='button';b.className='item-menu-button';b.append(icon('more'));b.draggable=false;
 b.setAttribute('aria-label',(target.type==='page'?'ページ「':'カテゴリ「')+target.label+'」のメニュー');b.setAttribute('aria-haspopup','menu');
 b.onclick=e=>{e.stopPropagation();openMenu(target,b.getBoundingClientRect(),b.parentElement);};
 return b;
}
function openMenu(target,rect,holder) {
 closeMenu();menuTarget={...target,holder};holder?.classList.add('menu-open');
 const menu=$('item-menu');menu.hidden=false;
 const left=Math.min(rect.left,innerWidth-menu.offsetWidth-8),top=rect.bottom+4+menu.offsetHeight>innerHeight?rect.top-menu.offsetHeight-4:rect.bottom+4;
 menu.style.left=Math.max(4,left)+'px';menu.style.top=Math.max(4,top)+'px';
 $('menu-delete-label').textContent=target.type==='page'?'ページをゴミ箱へ':'カテゴリをゴミ箱へ（中のページも）';
 $('menu-rename').focus();
}
function closeMenu(){$('item-menu').hidden=true;menuTarget?.holder?.classList.remove('menu-open');menuTarget=null;}
document.addEventListener('pointerdown',e=>{if(!$('item-menu').hidden&&!$('item-menu').contains(e.target))closeMenu();},{capture:true});
document.addEventListener('keydown',e=>{if(e.key==='Escape'&&!$('item-menu').hidden)closeMenu();},{capture:true});
$('pages').addEventListener('contextmenu',e=>{
 const t=e.target instanceof Element?e.target:null;const pb=t?.closest('.page-button'),ch=t?.closest('.category-heading');
 if(pb){e.preventDefault();openMenu({type:'page',id:pb.dataset.pageId,label:pageById(pb.dataset.pageId)?.title||''},{left:e.clientX,top:e.clientY,bottom:e.clientY},pb.parentElement);}
 else if(ch&&ch.dataset.category){e.preventDefault();openMenu({type:'category',name:ch.dataset.category,label:ch.dataset.category},{left:e.clientX,top:e.clientY,bottom:e.clientY},ch.parentElement);}
});
$('menu-rename').onclick=()=>{const t=menuTarget;closeMenu();if(!t)return;
 if(t.type==='page')showForm({kind:'rename-page',id:t.id},'ページの名前の変更',pageById(t.id)?.title||'','変更');
 else showForm({kind:'rename-category',name:t.name},'カテゴリの名前の変更',t.name,'変更');
};
$('menu-delete').onclick=()=>{const t=menuTarget;closeMenu();if(!t)return;
 finish();
 const entry=t.type==='page'?deletePage(doc,t.id):deleteCategory(doc,t.name);
 if(!entry)return;
 histories.delete(t.id);showPage();changed();
 message((t.type==='page'?'ページ「':'カテゴリ「')+(entry.name||'名称未設定')+'」をゴミ箱へ移動しました。左下の「ゴミ箱」から元に戻せます。');
};
const DEFAULT_NAME='名称未設定';
// Unique category name: 名称未設定, 名称未設定 2, 名称未設定 3 …
function uniqueCategoryName(base=DEFAULT_NAME) {
 normalizeCategories(doc);let name=base,n=2;
 while(doc.categories.includes(name))name=base+' '+n++;
 return name;
}
function showForm(mode,title,value,submitLabel) {
 formMode=mode;$('form-title').textContent=title;$('form-submit').textContent=submitLabel;
 const forPage=mode.kind==='rename-page'||mode.kind==='new-page';
 $('new-category-name').placeholder=forPage?'ページの名前（空欄なら「'+DEFAULT_NAME+'」）':'カテゴリ名（空欄なら「'+DEFAULT_NAME+'」）';$('new-category-name').maxLength=forPage?120:60;
 $('new-category').hidden=false;$('new-category-name').value=value;$('new-category-name').focus();$('new-category-name').select();
}
// ---- trash view ----
function renderTrash() {
 $('list-title').textContent='ゴミ箱';$('list-tip').textContent='「完全に削除」または「空にする」まで消えません';
 const back=document.createElement('button');back.type='button';back.className='trash-back';back.append(icon('back'),'ページ一覧へ戻る');back.onclick=()=>{view='pages';renderPages();};
 $('pages').append(back);
 const items=[...(doc.trash||[])].reverse();
 if(!items.length){const empty=document.createElement('div');empty.className='trash-empty';empty.textContent='ゴミ箱は空です';$('pages').append(empty);return;}
 for(const t of items){
  const item=document.createElement('div');item.className='trash-item';item.dataset.trashId=t.id;
  const name=document.createElement('span');name.className='trash-name';name.append(icon(t.kind==='page'?'file':'folder'),' '+(t.name||'名称未設定')+(t.kind==='category'?'（'+t.pages.length+'ページ）':''));
  const when=document.createElement('small');when.textContent='削除: '+new Date(t.deletedAt).toLocaleString('ja-JP');
  const row=document.createElement('div');
  const restore=document.createElement('button');restore.type='button';restore.className='restore';restore.append(icon('restore'),'元に戻す');
  restore.onclick=()=>{finish();const e=restoreTrash(doc,t.id);if(!e)return;view='pages';showPage();changed();message('「'+(e.name||'名称未設定')+'」を元に戻しました。');};
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
// ---- sidebar drag & drop (mouse) ----
const pagesEl=$('pages');
function clearDropMarks(){for(const el of pagesEl.querySelectorAll('.drop-before,.drop-after,.drop-into'))el.classList.remove('drop-before','drop-after','drop-into');}
function dropTarget(e) {
 const t=e.target instanceof Element?e.target:null;if(!t||!dragging)return null;
 const pb=t.closest('.page-button'),ch=t.closest('.category-heading'),grp=t.closest('.category');
 if(dragging.type==='page'){
  if(pb){if(pb.dataset.pageId===dragging.id)return null;const r=pb.getBoundingClientRect();return {mark:pb,cls:e.clientY<r.top+r.height/2?'drop-before':'drop-after',pageId:pb.dataset.pageId,category:grp.dataset.category};}
  if(grp)return {mark:grp,cls:'drop-into',category:grp.dataset.category};
  return null;
 }
 if(!grp||!grp.dataset.category||grp.dataset.category===dragging.name)return null;
 const r=grp.getBoundingClientRect();
 return {mark:ch||grp.querySelector('.category-heading'),cls:e.clientY<r.top+r.height/2?'drop-before':'drop-after',category:grp.dataset.category};
}
pagesEl.addEventListener('dragstart',e=>{
 const t=e.target instanceof Element?e.target:null;const pb=t?.closest('.page-button'),ch=t?.closest('.category-heading');
 if(pb){dragging={type:'page',id:pb.dataset.pageId};pb.classList.add('dragging');}
 else if(ch&&ch.dataset.category){dragging={type:'category',name:ch.dataset.category};ch.classList.add('dragging');}
 else{e.preventDefault();return;}
 e.dataTransfer.effectAllowed='move';try{e.dataTransfer.setData('text/plain',dragging.type);}catch{}
});
pagesEl.addEventListener('dragend',()=>{dragging=null;clearDropMarks();for(const el of pagesEl.querySelectorAll('.dragging'))el.classList.remove('dragging');});
pagesEl.addEventListener('dragover',e=>{
 if(!dragging)return;const t=dropTarget(e);clearDropMarks();if(!t)return;
 e.preventDefault();e.dataTransfer.dropEffect='move';t.mark.classList.add(t.cls);
});
pagesEl.addEventListener('dragleave',e=>{if(!pagesEl.contains(e.relatedTarget))clearDropMarks();});
pagesEl.addEventListener('drop',e=>{
 if(!dragging)return;e.preventDefault();const t=dropTarget(e),d=dragging;dragging=null;clearDropMarks();if(!t)return;
 let moved=false;
 if(d.type==='page'){
  if(t.cls==='drop-into')moved=movePage(doc,d.id,t.category,null);
  else if(t.cls==='drop-before')moved=movePage(doc,d.id,t.category,t.pageId);
  else{const list=doc.pages.filter(p=>categoryOf(p)===t.category),i=list.findIndex(p=>p.id===t.pageId);moved=movePage(doc,d.id,t.category,list[i+1]?list[i+1].id:null);}
  if(moved&&d.id===doc.activeId){$('page-category').value=page().category||'';breadcrumb();}
 } else {
  if(t.cls==='drop-before')moved=moveCategory(doc,d.name,t.category);
  else{const i=doc.categories.indexOf(t.category);moved=moveCategory(doc,d.name,doc.categories[i+1]||null);}
 }
 if(moved){changed();renderPages();}
});
// ---- add category ----
$('add-category').onclick=()=>showForm({kind:'new-category'},'新しいカテゴリ','','作成');
$('new-category-cancel').onclick=()=>{$('new-category').hidden=true;formMode=null;};
$('new-category').onsubmit=e=>{
 e.preventDefault();const mode=formMode||{kind:'new-category'};
 if(mode.kind==='rename-page'){
  const p=pageById(mode.id),title=$('new-category-name').value.trim()||DEFAULT_NAME;if(!p)return;
  p.title=title;$('new-category').hidden=true;formMode=null;
  if(p===page()){$('page-title').value=title;breadcrumb();}changed(p);renderPages();return;
 }
 if(mode.kind==='rename-category'){
  const wanted=$('new-category-name').value.trim()||uniqueCategoryName();
  const next=renameCategory(doc,mode.name,wanted);if(!next)return;
  $('new-category').hidden=true;formMode=null;collapsed.delete(next);
  $('page-category').value=page().category||'';breadcrumb();changed();renderPages();return;
 }
 if(mode.kind==='new-page'){
  const title=$('new-category-name').value.trim()||DEFAULT_NAME;
  if(doc.pages.length>=500){message('試作品では500ページまで作れます。');return;}
  $('new-category').hidden=true;formMode=null;finish();
  const p=newPage(title,categoryOf(page()));doc.pages.push(p);doc.activeId=p.id;showPage();changed();return;
 }
 const name=addCategory(doc,$('new-category-name').value.trim()||uniqueCategoryName());
 if(!name)return;formMode=null;
 $('new-category').hidden=true;collapsed.delete(name);
 if(doc.pages.some(p=>categoryOf(p)===name)){openPage(doc.pages.find(p=>categoryOf(p)===name).id);message('「'+name+'」はすでにあります。そのカテゴリのページを開きました。');renderPages();return;}
 if(doc.pages.length>=500){message('試作品では500ページまで作れます。');changed();renderPages();return;}
 finish();const p=newPage(DEFAULT_NAME,name);doc.pages.push(p);doc.activeId=p.id;showPage();changed();
 $('page-title').focus();$('page-title').select();
};
function breadcrumb(){const p=page(),c=categoryOf(p);$('breadcrumb').textContent=(c?c+' / ':'')+(p.title||'名称未設定');}
function showPage() {
 activeBlock=null;editing=null;selection={strokes:new Set(),blocks:new Set()};selectionLasso=null;ensureLayers(page());
 if(document.activeElement&&sheet.contains(document.activeElement))document.activeElement.blur();
 $('page-title').value=page().title;$('page-category').value=page().category||'';
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
 const p=page();scale=paper.clientWidth/W||1;
 sheet.style.setProperty('--ui-inverse-scale',1/scale);sheet.style.height=p.height+'px';sheet.style.transform='scale('+scale+')';lassoEl.setAttribute('height',p.height);
 paper.style.height=Math.round(p.height*scale)+'px';canvas.style.height=p.height+'px';
 const dpr=Math.min(devicePixelRatio||1,3);
 canvas.width=Math.max(1,Math.round(W*scale*dpr));canvas.height=Math.max(1,Math.round(p.height*scale*dpr));
 ctx.setTransform(canvas.width/W,0,0,canvas.height/p.height,0,0);
 $('page-size').textContent='ページの高さ '+p.height+' / 最大 '+MAX_HEIGHT;$('grow-page').disabled=!ready||p.height>=MAX_HEIGHT;
 redraw();
}
new ResizeObserver(()=>{if(paper.clientWidth!==lastPaperWidth){lastPaperWidth=paper.clientWidth;layout();}}).observe(paper);
function coordinates(e) {
 const rect=sheet.getBoundingClientRect();
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
 g.beginPath();g.moveTo(a[0],a[1]);g.lineTo(b[0],b[1]);g.stroke();dot(b,wb/2,s.color,g);
}
function drawStrokes(g,strokes) {
 for(const s of strokes){dot(s.points[0],inkWidth(s.width,s.points[0][2],s.pressure)/2,s.color,g);
  for(let i=1;i<s.points.length;i++)segment(s.points[i-1],s.points[i],s,g);
 }
}
// Layers are painted bottom to top. A translucent layer is drawn on an offscreen canvas
// first so overlapping strokes inside it do not darken each other.
function redraw() {
 if(!doc)return;const p=page();ensureLayers(p);
 ctx.save();ctx.setTransform(1,0,0,1,0,0);ctx.clearRect(0,0,canvas.width,canvas.height);ctx.restore();
 for(const L of p.layers){
  if(!L.visible)continue;const strokes=p.strokes.filter(s=>s.layer===L.id);if(!strokes.length)continue;
  if(L.opacity>=1){drawStrokes(ctx,strokes);continue;}
  if(off.width!==canvas.width||off.height!==canvas.height){off.width=canvas.width;off.height=canvas.height;}
  octx.setTransform(1,0,0,1,0,0);octx.clearRect(0,0,off.width,off.height);octx.setTransform(canvas.width/W,0,0,canvas.height/p.height,0,0);
  drawStrokes(octx,strokes);
  ctx.save();ctx.setTransform(1,0,0,1,0,0);ctx.globalAlpha=L.opacity;ctx.drawImage(off,0,0);ctx.restore();
 }
 updateHint();renderSelection();
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
 const p=page(),r=eraserRadius(),next=[],lid=p.activeLayer;let changed=false;
 for(const s of p.strokes){
  if(s.layer!==lid){next.push(s);continue;}
  if(eraserMode==='whole'){if(hitStroke(s,a,b,r))changed=true;else next.push(s);}
  else{const parts=erasePart(s,a,b,r);if(parts.length!==1||parts[0]!==s)changed=true;next.push(...parts);}
 }
 if(changed){p.strokes=next;gesture.changed=true;redraw();}
}
function startInk(e) {
 const L=editableLayer();if(!L)return;
 const point=inkPoint(e);
 const erasing=tool==='eraser'||(e.pointerType==='pen'&&(e.button===5||(e.buttons&32)!==0||(e.buttons&2)!==0));
 gesture={type:'ink',id:e.pointerId,pageId:doc.activeId,before:snapshot(page()),erase:erasing,last:point,changed:false,opacity:L.opacity};
 try{sheet.setPointerCapture(e.pointerId);}catch{}
 if(erasing)erase(point,point);
 else {
  const stroke={color,width,pressure:e.pointerType==='pen'&&$('pressure').checked,points:[point],layer:L.id};
  page().strokes=[...page().strokes,stroke];gesture.stroke=stroke;gesture.changed=true;redraw();
 }
}
function inputStatus(e){$('input-status').textContent=e.pointerType==='pen'?'ペン入力 · 筆圧 '+(e.pressure||0).toFixed(2):e.pointerType==='touch'?'タッチ':'マウス入力';}
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
sheet.addEventListener('pointerdown',e=>{
 if(!ready||gesture)return;
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
 const completed=gesture;gesture=null;
 if(sheet.hasPointerCapture?.(completed.id))sheet.releasePointerCapture(completed.id);
 if(completed.type==='ink')lastInkEnd=performance.now();
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
 if(completed.changed){const p=pageById(completed.pageId);if(p)commit(completed.before,p);if(completed.type==='ink')redraw();else{renderBlocks();redraw();}}
}
sheet.addEventListener('pointerleave',()=>{eraserCursor.hidden=true;});
for(const event of ['pointerup','pointercancel','lostpointercapture'])sheet.addEventListener(event,e=>{if(gesture&&e.pointerId===gesture.id)finish();});
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
try{const st=JSON.parse(localStorage.getItem('yohaku-layer-panel')||'null');if(st){if(st.left&&st.top)placePanel(parseFloat(st.left),parseFloat(st.top));if(st.collapsed)layerPanel.classList.add('collapsed');}}catch{}
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
$('page-category').oninput=e=>{page().category=e.target.value;breadcrumb();changed();};
$('page-category').onchange=e=>{const v=e.target.value.trim();e.target.value=v;page().category=v;if(v)addCategory(doc,v);changed();renderPages();};
$('grow-page').onclick=()=>{finish();const p=page(),before=snapshot(p);if(growPage(p,p.height+400))commit(before);};
$('add-page').onclick=()=>{
 if(doc.pages.length>=500){message('試作品では500ページまで作れます。');return;}
 const c=categoryOf(page());showForm({kind:'new-page'},'新しいページ'+(c?'（'+c+'）':''),'','作成');
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
  const added=incoming.pages.map(p=>({...p,id:crypto.randomUUID()}));
  const categories=[...(doc.categories||[]),...(incoming.categories||[]).filter(c=>!(doc.categories||[]).includes(c))];
  const merged=validateBackup({...doc,categories,pages:[...doc.pages,...added],activeId:added[0].id});
  doc=merged;for(const p of doc.pages)ensureLayers(p);showPage();changed();
  message(added.length+'ページを追加しました。元のページも残っています。');
 }catch(error){message('読み込めませんでした。元のメモは変更していません。 '+error.message);}
};
async function start() {
 try{
  db=await openStore();const saved=await loadNotebook(db);
  if(saved&&saved.version===1){
   const next=upgradeNotebook(saved);await migrateNotebook(db,saved,next);doc=next;
   message('以前のメモを新しい形式に変換しました。文章はページ内の入力欄に移し、手書きの位置はそのままです。変換前のデータもブラウザ内に残しています。');
  }
  else if(saved)doc=validateBackup(saved);
  else{const p=newPage('はじめのページ');doc={version:2,pages:[p],activeId:p.id};}
  let filled=false;for(const p of doc.pages)if(ensureLayers(p))filled=true;
  ready=true;document.querySelectorAll('button,input,textarea').forEach(el=>el.disabled=false);
  lastPaperWidth=paper.clientWidth;showPage();chooseTool('text');
  if(filled){revision++;dirty=true;save();}
  if(saved&&saved.version!==1)setStatus('保存済み');else changed();
  if('serviceWorker' in navigator)navigator.serviceWorker.register('./sw.js').catch(()=>message('オフライン起動の準備ができませんでした。通常の起動ファイルからは引き続き利用できます。'));
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
 function setLayers(opened){
  layerPanel.hidden=!opened;$('layers-toggle').setAttribute('aria-expanded',String(opened));
  if(opened&&layerPanel.classList.contains('collapsed'))$('layer-collapse').click();
 }
 $('layers-toggle').onclick=()=>setLayers(layerPanel.hidden);
 $('layer-close').onclick=()=>{setLayers(false);$('layers-toggle').focus();};
 setLayers(false);
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


