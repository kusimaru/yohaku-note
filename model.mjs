export const PAGE_WIDTH=1200, PAGE_HEIGHT=760, MAX_HEIGHT=6000, MAX_WIDTH=4800;
// pages start 1200 wide and grow to the right when writing reaches the edge (like they grow downwards)
export const pageWidth=p=>Number.isFinite(p?.width)&&p.width>PAGE_WIDTH?Math.min(MAX_WIDTH,p.width):PAGE_WIDTH;
// ---- rich text runs ----
// A text block stores plain `text` and optional `runs`: [{text,bold?,size?,color?}|{hr:true}].
export const DEFAULT_TEXT_COLOR='#2b3f38',MIN_FONT=8,MAX_FONT=72;
const sameFormat=(a,b)=>!!a.bold===!!b.bold&&(a.size||0)===(b.size||0)&&(a.color||'')===(b.color||'');
export function normalizeRuns(runs) {
 const out=[];
 for(const r of runs||[]){
  if(!r)continue;
  if(r.hr===true){out.push({hr:true});continue;}
  const text=String(r.text??'');if(!text)continue;
  const run={text};
  if(r.bold===true)run.bold=true;
  if(Number.isFinite(r.size)){const size=Math.round(r.size);if(size>=MIN_FONT&&size<=MAX_FONT)run.size=size;}
  if(typeof r.color==='string'&&/^#[0-9a-f]{6}$/i.test(r.color)&&r.color.toLowerCase()!==DEFAULT_TEXT_COLOR)run.color=r.color.toLowerCase();
  const last=out.at(-1);
  if(last&&!last.hr&&sameFormat(last,run))last.text+=text;else out.push(run);
 }
 return out;
}
export function runsToText(runs){return (runs||[]).map(r=>r.hr?'\n':r.text).join('');}
export function blockRuns(block){return block.runs?block.runs:(block.text?[{text:block.text}]:[]);}
function validateRuns(runs,bad) {
 if(!Array.isArray(runs)||runs.length>20000)bad();let total=0;
 for(const r of runs){
  if(!r||typeof r!=='object')bad();
  if(r.hr===true){if(Object.keys(r).length!==1)bad();continue;}
  for(const k of Object.keys(r))if(!['text','bold','size','color'].includes(k))bad();
  if(typeof r.text!=='string')bad();total+=r.text.length;if(total>200000)bad();
  if(r.bold!==undefined&&r.bold!==true)bad();
  if(r.size!==undefined&&(!Number.isInteger(r.size)||r.size<MIN_FONT||r.size>MAX_FONT))bad();
  if(r.color!==undefined&&!/^#[0-9a-f]{6}$/.test(r.color))bad();
 }
}
export function newTextBlock(x=64,y=64,text='') {
 return {id:crypto.randomUUID(),type:'text',x,y,width:Math.min(800,PAGE_WIDTH-x-24),height:120,text};
}
// ---- ink layers (handwriting only) ----
export const MAX_LAYERS=10;
export function newLayer(name='レイヤー 1'){return {id:crypto.randomUUID(),name,visible:true,locked:false,opacity:1};}
// Give every page a layer list and every stroke a layer id. Returns true when something was filled in.
export function ensureLayers(page) {
 let changed=false;
 if(!Array.isArray(page.layers)||!page.layers.length){page.layers=[newLayer()];changed=true;}
 const ids=new Set(page.layers.map(l=>l.id)),first=page.layers[0].id;
 for(const s of page.strokes)if(!ids.has(s.layer)){s.layer=first;changed=true;}
 if(!ids.has(page.activeLayer)){page.activeLayer=page.layers.at(-1).id;changed=true;}
 return changed;
}
export const activeLayerOf=page=>page.layers.find(l=>l.id===page.activeLayer)||page.layers.at(-1);
export function addLayer(page,name) {
 ensureLayers(page);if(page.layers.length>=MAX_LAYERS)return null;
 let n=page.layers.length+1,base=String(name||'').trim();
 if(!base){base='レイヤー '+n;while(page.layers.some(l=>l.name===base))base='レイヤー '+(++n);}
 const layer=newLayer(base.slice(0,40));page.layers=[...page.layers,layer];page.activeLayer=layer.id;return layer;
}
export function removeLayer(page,id) {
 ensureLayers(page);const i=page.layers.findIndex(l=>l.id===id);
 if(i<0||page.layers.length<2)return false;
 page.layers=page.layers.filter(l=>l.id!==id);page.strokes=page.strokes.filter(s=>s.layer!==id);
 if(page.activeLayer===id)page.activeLayer=page.layers[Math.min(i,page.layers.length-1)].id;
 return true;
}
export function updateLayer(page,id,patch) {
 ensureLayers(page);if(!page.layers.some(l=>l.id===id))return false;
 page.layers=page.layers.map(l=>l.id===id?{...l,...patch}:l);return true;
}
// Move layer `id` so that it sits at index `toIndex` (0 = bottom).
export function moveLayer(page,id,toIndex) {
 ensureLayers(page);const layer=page.layers.find(l=>l.id===id);if(!layer)return false;
 const rest=page.layers.filter(l=>l.id!==id),index=Math.max(0,Math.min(rest.length,toIndex));
 rest.splice(index,0,layer);page.layers=rest;return true;
}
export function newPage(title='新しいページ',sectionId='') {
 const layer=newLayer();
 const p={id:crypto.randomUUID(),title,blocks:[newTextBlock()],height:1200,strokes:[],layers:[layer],activeLayer:layer.id,updatedAt:Date.now()};
 if(sectionId)p.sectionId=sectionId;return p;
}
export function inkWidth(width,pressure,enabled) {
 return width*(enabled?.25+Math.max(0,Math.min(1,pressure))*1.5:1);
}
function pointDistance(p,a,b) {
 const dx=b[0]-a[0],dy=b[1]-a[1];
 const t=Math.max(0,Math.min(1,((p[0]-a[0])*dx+(p[1]-a[1])*dy)/(dx*dx+dy*dy||1)));
 return Math.hypot(p[0]-a[0]-t*dx,p[1]-a[1]-t*dy);
}
function cross(a,b,c){return(b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]);}
function distance(a,b,c,d) {
 const x=cross(a,b,c),y=cross(a,b,d),z=cross(c,d,a),w=cross(c,d,b);
 if(((x>0&&y<0)||(x<0&&y>0))&&((z>0&&w<0)||(z<0&&w>0)))return 0;
 return Math.min(pointDistance(a,c,d),pointDistance(b,c,d),pointDistance(c,a,b),pointDistance(d,a,b));
}
export function hitStroke(s,a,b,radius) {
 for(let i=0;i<s.points.length;i++)if(distance(a,b,s.points[Math.max(0,i-1)],s.points[i])<=radius+s.width*1.75/2)return true;
 return false;
}
const mix=(a,b,t)=>a.map((v,i)=>v+(b[i]-v)*t);
function sampleStroke(s) {
 const samples=[s.points[0]];
 for(let i=1;i<s.points.length;i++){
  const p=s.points[i-1],q=s.points[i],n=Math.max(1,Math.ceil(Math.hypot(q[0]-p[0],q[1]-p[1])/1.5));
  for(let j=1;j<=n;j++)samples.push(j===n?q:mix(p,q,j/n));
 }
 return samples;
}
// Split a stroke into fragments where `inside(point)` holds and where it does not.
// Fragments keep colour/width/pressure; boundary points are located by bisection so
// each fragment ends on its own side of the boundary.
const MIN_FRAGMENT=2; // px: slivers shorter than this (a stroke grazing the boundary) join the previous piece
const polyLength=pts=>{let n=0;for(let i=1;i<pts.length;i++)n+=Math.hypot(pts[i][0]-pts[i-1][0],pts[i][1]-pts[i-1][1]);return n;};
export function partitionStroke(s,inside) {
 const samples=sampleStroke(s),result={true:[],false:[]};
 let fragment=[],current=inside(samples[0]),last=null;
 const flush=()=>{
  if(!fragment.length)return false;
  if(last&&polyLength(fragment)<MIN_FRAGMENT){last.points.push(...fragment);fragment=[];return true;}
  last={...s,points:fragment};result[current].push(last);fragment=[];return false;
 };
 for(let i=0;i<samples.length;i++){
  const p=samples[i],cut=inside(p);
  if(cut!==current){
   let lo=0,hi=1;const prev=samples[i-1];
   for(let j=0;j<14;j++){const mid=(lo+hi)/2;if(inside(mix(prev,p,mid))===current)lo=mid;else hi=mid;}
   fragment.push(mix(prev,p,lo));const merged=flush();current=cut;
   // a sliver was folded into the previous piece: keep extending that piece instead of opening a new one
   if(merged){const arr=result[current];if(arr[arr.length-1]===last){arr.pop();fragment=last.points;}}
   fragment.push(mix(prev,p,hi));
  }
  fragment.push(p);
 }
 flush();
 return {inside:result[true],outside:result[false]};
}
// Clip the centreline against the swept eraser capsule. Include the ink radius
// so rounded fragment ends cannot paint back into the erased area.
export function erasePart(s,a,b,radius) {
 if(!hitStroke(s,a,b,radius))return[s];
 const parts=partitionStroke(s,p=>pointDistance(p,a,b)<=radius+inkWidth(s.width,p[2],s.pressure)/2);
 return parts.inside.length?parts.outside:[s];
}
export function pointInPolygon(p,polygon) {
 let inside=false;
 for(let i=0,j=polygon.length-1;i<polygon.length;j=i++){
  const a=polygon[i],b=polygon[j];
  if((a[1]>p[1])!==(b[1]>p[1])&&p[0]<(b[0]-a[0])*(p[1]-a[1])/(b[1]-a[1])+a[0])inside=!inside;
 }
 return inside;
}
// Lasso: the part of the stroke enclosed by the polygon becomes its own stroke(s).
// Returns the same stroke object untouched when it is entirely inside or outside.
export function splitByPolygon(s,polygon) {
 if(polygon.length<3)return {inside:[],outside:[s]};
 const parts=partitionStroke(s,p=>pointInPolygon(p,polygon));
 if(!parts.inside.length)return {inside:[],outside:[s]};
 if(!parts.outside.length)return {inside:[s],outside:[]};
 return parts;
}
// ---- notebooks › sections › pages (OneNote-like) ----
export const SECTION_COLORS=['#c2185b','#1e5bb8','#2e9e5b','#d94a3d','#7b3fb0','#e08a00','#0f9c8a','#5c6bc0','#8d6e63','#546e7a'];
export const DEFAULT_NOTEBOOK_ID='nb:default';
export const categoryOf=p=>(p.category||'').trim(); // legacy field from the single-level version
const pickColor=i=>SECTION_COLORS[i%SECTION_COLORS.length];
const cleanName=(name,fallback)=>String(name??'').trim().slice(0,60)||fallback;
function uniqueName(names,base){let n=base,i=2;while(names.includes(n))n=base+' '+i++;return n;}
export function newNotebook(name,color){return {id:crypto.randomUUID(),name:cleanName(name,'新しいノートブック'),color:color||pickColor(0)};}
export function newSection(notebookId,name,color){return {id:crypto.randomUUID(),notebookId,name:cleanName(name,'新しいセクション'),color:color||pickColor(0)};}
export const notebookOf=(doc,id)=>(doc.notebooks||[]).find(n=>n.id===id);
export const sectionOf=(doc,id)=>(doc.sections||[]).find(s=>s.id===id);
export const sectionsIn=(doc,notebookId)=>(doc.sections||[]).filter(s=>s.notebookId===notebookId);
export const pagesIn=(doc,sectionId)=>doc.pages.filter(p=>p.sectionId===sectionId);
// Fill in the structure: a default notebook, sections migrated from the old category names
// (deterministic ids so two devices migrate the same way), and every page inside a section.
// A page that points at a section this device does not know yet gets a placeholder section
// (the real name arrives later through sync). Returns true when anything was changed.
export function ensureStructure(doc) {
 let changed=false;
 if(!Array.isArray(doc.notebooks)||!doc.notebooks.length){doc.notebooks=[{id:DEFAULT_NOTEBOOK_ID,name:'わたしのノート',color:pickColor(0)}];changed=true;}
 if(!Array.isArray(doc.sections)){doc.sections=[];changed=true;}
 const home=doc.notebooks[0].id,nbIds=new Set(doc.notebooks.map(n=>n.id));
 for(const s of doc.sections)if(!nbIds.has(s.notebookId)){doc.notebooks.push({id:s.notebookId,name:'同期待ち',color:pickColor(doc.notebooks.length),placeholder:true,updatedAt:0});nbIds.add(s.notebookId);changed=true;}
 const byId=id=>doc.sections.find(s=>s.id===id);
 const legacy=[...(doc.categories||[]),...doc.pages.map(p=>categoryOf(p))].filter(Boolean);
 for(const name of legacy){
  if(byId('sec:'+name)||doc.sections.some(s=>s.notebookId===home&&s.name===name))continue;
  doc.sections.push({id:'sec:'+name,notebookId:home,name,color:pickColor(doc.sections.length)});changed=true;
 }
 const memo=()=>{let m=byId('sec:メモ');if(!m){m={id:'sec:メモ',notebookId:home,name:'メモ',color:pickColor(doc.sections.length)};doc.sections.push(m);changed=true;}return m;};
 for(const p of doc.pages){
  if(typeof p.sectionId==='string'&&p.sectionId){
   if(!byId(p.sectionId)){doc.sections.push({id:p.sectionId,notebookId:home,name:'同期待ち',color:pickColor(doc.sections.length),placeholder:true,updatedAt:0});changed=true;}
  } else {
   const name=categoryOf(p);
   const sec=name?(byId('sec:'+name)||doc.sections.find(s=>s.notebookId===home&&s.name===name)||memo()):memo();
   p.sectionId=sec.id;changed=true;
  }
  if(p.category!==undefined){delete p.category;changed=true;}
 }
 if(!doc.sections.length){memo();}
 if(doc.categories!==undefined){delete doc.categories;changed=true;}
 return changed;
}
// ---------- structure sync: per-item "newest wins" merge (notebooks, sections, tombstones, orders) ----------
// Every notebook/section carries updatedAt (0 = never stamped). doc.removed = {id: deletedAt} tombstones.
// doc.orderUpdatedAt stamps the three orderings (notebooks, sections, pages) as one unit.
const HEX=/^#[0-9a-f]{6}$/i;
const itemKey=x=>JSON.stringify({...x,updatedAt:undefined,placeholder:undefined});
const cleanNotebook=n=>n&&typeof n.id==='string'&&n.id.length<=100&&typeof n.name==='string'&&n.name.trim()&&HEX.test(n.color||'')?{id:n.id,name:n.name.slice(0,60),color:n.color.toLowerCase(),updatedAt:Number.isFinite(n.updatedAt)?n.updatedAt:0,...(n.placeholder?{placeholder:true}:{})}:null;
const cleanSection=x=>x&&typeof x.id==='string'&&x.id.length<=100&&typeof x.notebookId==='string'&&typeof x.name==='string'&&x.name.trim()&&HEX.test(x.color||'')?{id:x.id,notebookId:x.notebookId,name:x.name.slice(0,60),color:x.color.toLowerCase(),updatedAt:Number.isFinite(x.updatedAt)?x.updatedAt:0,...(x.placeholder?{placeholder:true}:{})}:null;
export function removedOf(doc){const out={};const r=doc.removed;if(Array.isArray(r)){for(const e of r)if(e&&typeof e.id==='string'&&Number.isFinite(e.at))out[e.id]=e.at;}else if(r&&typeof r==='object'){for(const [id,at] of Object.entries(r))if(Number.isFinite(at))out[id]=at;}return out;}
// Which of two same-id versions wins: newer stamp; then a real item over a placeholder; then the larger JSON (deterministic on both devices).
function better(a,b){
 if(!a)return b;if(!b)return a;
 const ta=a.updatedAt||0,tb=b.updatedAt||0;if(ta!==tb)return ta>tb?a:b;
 if(!!a.placeholder!==!!b.placeholder)return a.placeholder?b:a;
 return itemKey(a)>=itemKey(b)?a:b;
}
function mergeList(local,remote,removed){
 const ids=[...new Set([...local.map(x=>x.id),...remote.map(x=>x.id)])],out=[];
 for(const id of ids){
  const w=better(local.find(x=>x.id===id),remote.find(x=>x.id===id)),dead=removed[id];
  if(dead!==undefined&&dead>=(w.updatedAt||0))continue; // deleted after its last edit (a later restore re-stamps it)
  out.push(w);
 }
 return out;
}
// Order: take the id sequence from the side with the newer orderUpdatedAt (tie: larger JSON), then append the rest.
function orderBy(items,baseIds,otherIds){
 const pos=new Map(baseIds.map((id,i)=>[id,i]));const rest=items.filter(x=>!pos.has(x.id));
 const restPos=new Map(otherIds.map((id,i)=>[id,i]));rest.sort((a,b)=>(restPos.get(a.id)??1e9)-(restPos.get(b.id)??1e9));
 return [...items.filter(x=>pos.has(x.id)).sort((a,b)=>pos.get(a.id)-pos.get(b.id)),...rest];
}
export function structureSig(doc){return JSON.stringify([(doc.notebooks||[]).map(cleanNotebook),(doc.sections||[]).map(cleanSection),Object.entries(removedOf(doc)).sort(),doc.pages.map(p=>p.id)]);}
export function mergeStructure(doc,remote) {
 ensureStructure(doc);
 const before=structureSig(doc);
 const rNotebooks=(Array.isArray(remote.notebooks)?remote.notebooks:[]).map(cleanNotebook).filter(Boolean);
 const rSections=(Array.isArray(remote.sections)?remote.sections:[]).map(cleanSection).filter(Boolean);
 const removed=removedOf(doc),rRemoved=removedOf(remote);
 for(const [id,at] of Object.entries(rRemoved))if(!(removed[id]>=at))removed[id]=at;
 const localNb=(doc.notebooks||[]).map(cleanNotebook).filter(Boolean),localSec=(doc.sections||[]).map(cleanSection).filter(Boolean);
 let notebooks=mergeList(localNb,rNotebooks,removed),sections=mergeList(localSec,rSections,removed);
 const lo=doc.orderUpdatedAt||0,ro=remote.orderUpdatedAt||0;
 const rOrder=Array.isArray(remote.order)?remote.order.filter(x=>typeof x==='string'):[];
 const remoteWins=ro>lo||(ro===lo&&JSON.stringify([rNotebooks.map(x=>x.id),rSections.map(x=>x.id),rOrder])>JSON.stringify([localNb.map(x=>x.id),localSec.map(x=>x.id),doc.pages.map(x=>x.id)]));
 const base=remoteWins?{nb:rNotebooks.map(x=>x.id),sec:rSections.map(x=>x.id),pg:rOrder}:{nb:localNb.map(x=>x.id),sec:localSec.map(x=>x.id),pg:doc.pages.map(x=>x.id)};
 const other=remoteWins?{nb:localNb.map(x=>x.id),sec:localSec.map(x=>x.id),pg:doc.pages.map(x=>x.id)}:{nb:rNotebooks.map(x=>x.id),sec:rSections.map(x=>x.id),pg:rOrder};
 notebooks=orderBy(notebooks,base.nb,other.nb);sections=orderBy(sections,base.sec,other.sec);
 doc.notebooks=notebooks;doc.sections=sections;doc.removed=removed;doc.orderUpdatedAt=Math.max(lo,ro);
 doc.pages=orderBy(doc.pages,base.pg,other.pg);
 // keep the tombstone list bounded
 const entries=Object.entries(removed);if(entries.length>1000){entries.sort((a,b)=>b[1]-a[1]);doc.removed=Object.fromEntries(entries.slice(0,1000));}
 ensureStructure(doc);
 const after=structureSig(doc);
 const remoteSig=JSON.stringify([rNotebooks,rSections,Object.entries(rRemoved).sort(),rOrder]);
 return {localChanged:before!==after,remoteDiffers:after!==remoteSig};
}
// Called after local edits: stamps items that changed since `prev` (a snapshot from a previous call), records tombstones
// for items that vanished, and stamps the orderings when they moved. Placeholders created by ensureStructure are not stamped.
export function observeStructure(doc,prev,now=Date.now()) {
 ensureStructure(doc);
 const items=new Map();let changed=false;
 for(const x of [...doc.notebooks,...doc.sections]){
  const key=itemKey(x),old=prev?prev.items.get(x.id):undefined;
  if(old===undefined){if(prev&&!x.placeholder){x.updatedAt=now;changed=true;}}
  else if(old!==key){x.updatedAt=now;delete x.placeholder;changed=true;}
  items.set(x.id,itemKey(x));
 }
 if(prev){const removed=removedOf(doc);for(const id of prev.items.keys())if(!items.has(id)){removed[id]=now;changed=true;doc.removed=removed;}}
 const order=JSON.stringify([doc.notebooks.map(x=>x.id),doc.sections.map(x=>x.id),doc.pages.map(x=>x.id)]);
 if(prev&&prev.order!==order){doc.orderUpdatedAt=now;changed=true;}
 return {snapshot:{items,order},changed};
}
export function structureMeta(doc){return {notebooks:(doc.notebooks||[]).map(cleanNotebook).filter(Boolean),sections:(doc.sections||[]).map(cleanSection).filter(Boolean),removed:Object.entries(removedOf(doc)).map(([id,at])=>({id,at})),order:doc.pages.map(p=>p.id),orderUpdatedAt:doc.orderUpdatedAt||0,updatedAt:doc.metaUpdatedAt||Date.now()};}
export function addNotebook(doc,name) {
 ensureStructure(doc);
 const nb=newNotebook(name||uniqueName(doc.notebooks.map(n=>n.name),'新しいノートブック'),pickColor(doc.notebooks.length));
 doc.notebooks.push(nb);return nb;
}
export function addSection(doc,notebookId,name) {
 ensureStructure(doc);if(!notebookOf(doc,notebookId))return null;
 const sibs=sectionsIn(doc,notebookId);
 const sec=newSection(notebookId,name||uniqueName(sibs.map(s=>s.name),'新しいセクション'),pickColor(doc.sections.length));
 doc.sections.push(sec);return sec;
}
export function renameNotebook(doc,id,name){const nb=notebookOf(doc,id),t=String(name??'').trim();if(!nb||!t||t.length>60)return null;nb.name=t;return t;}
export function renameSection(doc,id,name){const sec=sectionOf(doc,id),t=String(name??'').trim();if(!sec||!t||t.length>60)return null;sec.name=t;return t;}
export function setSectionColor(doc,id,color){const sec=sectionOf(doc,id);if(!sec||!/^#[0-9a-f]{6}$/i.test(color||''))return false;sec.color=color.toLowerCase();return true;}
export function setNotebookColor(doc,id,color){const nb=notebookOf(doc,id);if(!nb||!/^#[0-9a-f]{6}$/i.test(color||''))return false;nb.color=color.toLowerCase();return true;}
// Move a page into `sectionId`, placed before page `beforeId` (same section) or at the end.
export function movePage(doc,pageId,sectionId,beforeId=null) {
 const p=doc.pages.find(x=>x.id===pageId);if(!p||beforeId===pageId||!sectionOf(doc,sectionId))return false;
 const rest=doc.pages.filter(x=>x.id!==pageId);p.sectionId=sectionId;
 let index=beforeId?rest.findIndex(x=>x.id===beforeId&&x.sectionId===sectionId):-1;
 if(index<0){index=rest.length;for(let i=rest.length-1;i>=0;i--)if(rest[i].sectionId===sectionId){index=i+1;break;}}
 rest.splice(index,0,p);doc.pages=rest;return true;
}
export function moveSection(doc,id,notebookId,beforeId=null) {
 const sec=sectionOf(doc,id);if(!sec||!notebookOf(doc,notebookId)||beforeId===id)return false;
 const rest=doc.sections.filter(x=>x.id!==id);sec.notebookId=notebookId;
 let index=beforeId?rest.findIndex(x=>x.id===beforeId&&x.notebookId===notebookId):-1;
 if(index<0){index=rest.length;for(let i=rest.length-1;i>=0;i--)if(rest[i].notebookId===notebookId){index=i+1;break;}}
 rest.splice(index,0,sec);doc.sections=rest;return true;
}
export function moveNotebook(doc,id,beforeId=null) {
 const nb=notebookOf(doc,id);if(!nb||beforeId===id)return false;
 const rest=doc.notebooks.filter(x=>x.id!==id);const index=beforeId?rest.findIndex(x=>x.id===beforeId):-1;
 rest.splice(index<0?rest.length:index,0,nb);doc.notebooks=rest;return true;
}
// ---- trash ----
function ensureActive(doc,removedIndex) {
 ensureStructure(doc);
 if(!doc.pages.length){const p=newPage('はじめのページ',doc.sections[0].id);doc.pages.push(p);}
 if(!doc.pages.some(p=>p.id===doc.activeId))doc.activeId=doc.pages[Math.min(Math.max(0,removedIndex),doc.pages.length-1)].id;
}
export function deletePage(doc,id) {
 const i=doc.pages.findIndex(p=>p.id===id);if(i<0)return null;
 const [p]=doc.pages.splice(i,1);
 const entry={id:crypto.randomUUID(),kind:'page',name:p.title,pages:[p],deletedAt:Date.now()};
 (doc.trash??=[]).push(entry);ensureActive(doc,i);return entry;
}
export function deleteSection(doc,id) {
 ensureStructure(doc);const sec=sectionOf(doc,id);if(!sec)return null;
 const first=doc.pages.findIndex(p=>p.sectionId===id);
 const pages=doc.pages.filter(p=>p.sectionId===id);doc.pages=doc.pages.filter(p=>p.sectionId!==id);
 doc.sections=doc.sections.filter(s=>s.id!==id);
 const entry={id:crypto.randomUUID(),kind:'section',name:sec.name,section:{...sec},pages,deletedAt:Date.now()};
 (doc.trash??=[]).push(entry);ensureActive(doc,first<0?0:first);return entry;
}
export function deleteNotebook(doc,id) {
 ensureStructure(doc);const nb=notebookOf(doc,id);if(!nb||doc.notebooks.length<2)return null;
 const sections=sectionsIn(doc,id),secIds=new Set(sections.map(s=>s.id));
 const first=doc.pages.findIndex(p=>secIds.has(p.sectionId));
 const pages=doc.pages.filter(p=>secIds.has(p.sectionId));doc.pages=doc.pages.filter(p=>!secIds.has(p.sectionId));
 doc.sections=doc.sections.filter(s=>!secIds.has(s.id));doc.notebooks=doc.notebooks.filter(n=>n.id!==id);
 const entry={id:crypto.randomUUID(),kind:'notebook',name:nb.name,notebook:{...nb},sections:sections.map(s=>({...s})),pages,deletedAt:Date.now()};
 (doc.trash??=[]).push(entry);ensureActive(doc,first<0?0:first);return entry;
}
export function restoreTrash(doc,entryId) {
 const i=(doc.trash||[]).findIndex(t=>t.id===entryId);if(i<0)return null;
 const [entry]=doc.trash.splice(i,1);ensureStructure(doc);
 const home=doc.notebooks[0].id;
 if(entry.kind==='notebook'){
  if(!notebookOf(doc,entry.notebook.id))doc.notebooks.push({...entry.notebook});
  for(const s of entry.sections||[])if(!sectionOf(doc,s.id))doc.sections.push({...s,notebookId:entry.notebook.id});
 } else if(entry.kind==='section'){
  const s=entry.section||{id:'sec:'+entry.name,name:entry.name,color:pickColor(doc.sections.length)};
  if(!sectionOf(doc,s.id))doc.sections.push({...s,notebookId:notebookOf(doc,s.notebookId)?s.notebookId:home});
  for(const p of entry.pages)p.sectionId=s.id;
 } else if(entry.kind==='category'){
  let s=doc.sections.find(x=>x.notebookId===home&&x.name===entry.name);
  if(!s){s={id:'sec:'+entry.name,notebookId:home,name:entry.name,color:pickColor(doc.sections.length)};doc.sections.push(s);}
  for(const p of entry.pages){p.sectionId=s.id;delete p.category;}
 }
 for(const p of entry.pages){
  if(doc.pages.some(x=>x.id===p.id))p.id=crypto.randomUUID();
  if(!sectionOf(doc,p.sectionId))p.sectionId=doc.sections[0].id;
  doc.pages.push(p);movePage(doc,p.id,p.sectionId);
 }
 ensureStructure(doc);
 if(entry.pages[0])doc.activeId=entry.pages[0].id;
 return entry;
}
export function purgeTrash(doc,entryId) {
 const i=(doc.trash||[]).findIndex(t=>t.id===entryId);if(i<0)return false;
 doc.trash.splice(i,1);return true;
}
export function emptyTrash(doc){const n=(doc.trash||[]).length;doc.trash=[];return n;}
// Merge a backup from another device: same page id → keep the newer one (by updatedAt),
// unknown id → add, id sitting in this notebook's trash → leave in the trash. Notebooks,
// sections and trash entries are unioned by id. Returns counts for the user.
export function mergeNotebook(doc,incoming) {
 const result={added:0,updated:0,unchanged:0,skipped:0};
 ensureStructure(doc);ensureStructure(incoming);
 for(const nb of incoming.notebooks)if(!notebookOf(doc,nb.id))doc.notebooks.push({...nb});
 for(const sec of incoming.sections)if(!sectionOf(doc,sec.id))doc.sections.push({...sec});
 const trashIds=new Set((doc.trash||[]).flatMap(t=>t.pages.map(p=>p.id)));
 for(const p of incoming.pages){
  const i=doc.pages.findIndex(x=>x.id===p.id);
  if(i>=0){if((p.updatedAt||0)>(doc.pages[i].updatedAt||0)){doc.pages[i]=p;result.updated++;}else result.unchanged++;continue;}
  if(trashIds.has(p.id)){result.skipped++;continue;}
  doc.pages.push(p);result.added++;
 }
 const trashSeen=new Set((doc.trash||[]).map(t=>t.id));
 doc.trash=[...(doc.trash||[]),...(incoming.trash||[]).filter(t=>!trashSeen.has(t.id)&&!t.pages.some(pg=>doc.pages.some(x=>x.id===pg.id)))];
 ensureStructure(doc);for(const pg of doc.pages)ensureLayers(pg);
 if(!doc.pages.some(x=>x.id===doc.activeId))doc.activeId=doc.pages[0].id;
 return result;
}
export function validateBackup(doc) {
 const bad=()=>{throw new Error('対応するノートデータではないか、試作品の上限を超えています。');};
 if(!doc||![1,2].includes(doc.version)||!Array.isArray(doc.pages)||doc.pages.length<1||doc.pages.length>500)bad();
 if(doc.categories!==undefined){
  if(!Array.isArray(doc.categories)||doc.categories.length>500)bad();const seen=new Set();
  for(const c of doc.categories){if(typeof c!=='string'||!c.trim()||c.length>60||seen.has(c))bad();seen.add(c);}
 }
 const hex=/^#[0-9a-f]{6}$/i,nbIds=new Set(),secIds=new Set();
 const checkNotebook=n=>{if(!n||typeof n.id!=='string'||n.id.length>100||nbIds.has(n.id)||typeof n.name!=='string'||!n.name.trim()||n.name.length>60||!hex.test(n.color||''))bad();nbIds.add(n.id);};
 const checkSection=x=>{if(!x||typeof x.id!=='string'||x.id.length>100||secIds.has(x.id)||typeof x.notebookId!=='string'||x.notebookId.length>100||typeof x.name!=='string'||!x.name.trim()||x.name.length>60||!hex.test(x.color||''))bad();secIds.add(x.id);};
 if(doc.notebooks!==undefined){if(!Array.isArray(doc.notebooks)||doc.notebooks.length>100)bad();for(const n of doc.notebooks)checkNotebook(n);}
 if(doc.sections!==undefined){if(!Array.isArray(doc.sections)||doc.sections.length>500)bad();for(const x of doc.sections)checkSection(x);}
 const ids=new Set();let points=0,totalImages=0;
 const checkPage=p=>{
  if(!p||typeof p.id!=='string'||p.id.length>100||ids.has(p.id)||typeof p.title!=='string'||p.title.length>120||
   !Number.isFinite(p.updatedAt)||!Array.isArray(p.strokes)||p.strokes.length>50000)bad();
  if(p.category!==undefined&&(typeof p.category!=='string'||p.category.length>60))bad();
  if(p.sectionId!==undefined&&(typeof p.sectionId!=='string'||!p.sectionId||p.sectionId.length>100))bad();
  ids.add(p.id);
  const height=doc.version===1?PAGE_HEIGHT:p.height,width=p.width===undefined?PAGE_WIDTH:p.width;
  if(!Number.isFinite(height)||height<760||height>MAX_HEIGHT)bad();
  if(!Number.isFinite(width)||width<PAGE_WIDTH||width>MAX_WIDTH)bad();
  if(doc.version===1){if(typeof p.text!=='string'||p.text.length>200000)bad();}
  else {
   if(!Array.isArray(p.blocks)||p.blocks.length>1000)bad();const blockIds=new Set();
   for(const o of p.blocks){
    if(!o||typeof o.id!=='string'||o.id.length>100||blockIds.has(o.id)||!['text','image'].includes(o.type)||
     ![o.x,o.y,o.width,o.height].every(Number.isFinite)||o.x<0||o.y<0||o.width<40||o.height<24||
     o.x+o.width>width+.01||o.y+o.height>height+.01)bad();
    blockIds.add(o.id);
    if(o.type==='text'){if(typeof o.text!=='string'||o.text.length>200000)bad();if(o.runs!==undefined)validateRuns(o.runs,bad);}
    else {if(typeof o.src!=='string'||!/^data:image\/(png|jpeg|webp);base64,[A-Za-z0-9+/=]+$/.test(o.src)||o.src.length>16000000)bad();totalImages+=o.src.length;if(totalImages>65000000)bad();}
   }
  }
  let layerIds=null;
  if(p.layers!==undefined){
   if(!Array.isArray(p.layers)||p.layers.length<1||p.layers.length>MAX_LAYERS)bad();layerIds=new Set();
   for(const l of p.layers){
    if(!l||typeof l.id!=='string'||l.id.length>100||layerIds.has(l.id)||typeof l.name!=='string'||l.name.length>40||
     typeof l.visible!=='boolean'||typeof l.locked!=='boolean'||!Number.isFinite(l.opacity)||l.opacity<0||l.opacity>1)bad();
    layerIds.add(l.id);
   }
   if(p.activeLayer!==undefined&&!layerIds.has(p.activeLayer))bad();
  }
  for(const s of p.strokes){
   if(!s||!/^#[0-9a-f]{6}$/i.test(s.color)||!Number.isFinite(s.width)||s.width<1||s.width>24||
    typeof s.pressure!=='boolean'||!Array.isArray(s.points)||s.points.length<1)bad();
   if(s.layer!==undefined&&(typeof s.layer!=='string'||s.layer.length>100||(layerIds&&!layerIds.has(s.layer))))bad();
   points+=s.points.length;if(points>2000000)bad();
   for(const pt of s.points)if(!Array.isArray(pt)||pt.length!==3||!pt.every(Number.isFinite)||pt[0]<0||pt[0]>width||pt[1]<0||pt[1]>height||pt[2]<0||pt[2]>1)bad();
  }
 };
 for(const p of doc.pages)checkPage(p);
 if(!ids.has(doc.activeId))bad();
 if(doc.trash!==undefined){
  if(!Array.isArray(doc.trash)||doc.trash.length>500)bad();
  for(const t of doc.trash){
   if(!t||typeof t.id!=='string'||t.id.length>100||ids.has(t.id)||!['page','category','section','notebook'].includes(t.kind)||typeof t.name!=='string'||t.name.length>120||
    !Number.isFinite(t.deletedAt)||!Array.isArray(t.pages)||t.pages.length>500||(t.kind==='page'&&t.pages.length!==1))bad();
   if(t.kind==='section'&&t.section!==undefined){const x=t.section;if(!x||typeof x.id!=='string'||typeof x.name!=='string'||x.name.length>60||!hex.test(x.color||''))bad();}
   if(t.kind==='notebook'){const n=t.notebook;if(!n||typeof n.id!=='string'||typeof n.name!=='string'||n.name.length>60||!hex.test(n.color||''))bad();if(!Array.isArray(t.sections)||t.sections.length>500)bad();for(const x of t.sections)if(!x||typeof x.id!=='string'||typeof x.name!=='string'||x.name.length>60||!hex.test(x.color||''))bad();}
   ids.add(t.id);for(const p of t.pages)checkPage(p);
  }
 }
 return doc;
}
export function upgradeNotebook(input) {
 validateBackup(input);if(input.version===2)return structuredClone(input);
 const doc=structuredClone(input);doc.version=2;
 for(const p of doc.pages){
  const y=p.strokes.length?820:64;
  p.blocks=[newTextBlock(64,y,p.text)];p.height=Math.max(1200,y+280);
  delete p.text;
 }
 return validateBackup(doc);
}

