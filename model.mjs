export const PAGE_WIDTH=1200, PAGE_HEIGHT=760, MAX_HEIGHT=6000;
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
export function newPage(title='新しいページ',category='') {
 const layer=newLayer();
 return {id:crypto.randomUUID(),title,category,blocks:[newTextBlock()],height:1200,strokes:[],layers:[layer],activeLayer:layer.id,updatedAt:Date.now()};
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
export function partitionStroke(s,inside) {
 const samples=sampleStroke(s),result={true:[],false:[]};
 let fragment=[],current=inside(samples[0]);
 const flush=()=>{if(fragment.length)result[current].push({...s,points:fragment});fragment=[];};
 for(let i=0;i<samples.length;i++){
  const p=samples[i],cut=inside(p);
  if(cut!==current){
   let lo=0,hi=1;const prev=samples[i-1];
   for(let j=0;j<14;j++){const mid=(lo+hi)/2;if(inside(mix(prev,p,mid))===current)lo=mid;else hi=mid;}
   fragment.push(mix(prev,p,lo));flush();current=cut;fragment.push(mix(prev,p,hi));
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
export const categoryOf=p=>(p.category||'').trim();
// Keep doc.categories as the ordered list of sections: stored order first, then any
// category that only exists on pages. Empty categories stay so they can hold pages later.
export function normalizeCategories(doc) {
 const list=[],seen=new Set();
 for(const c of doc.categories||[]){const t=String(c).trim();if(t&&!seen.has(t)){seen.add(t);list.push(t);}}
 for(const p of doc.pages){const c=categoryOf(p);if(c&&!seen.has(c)){seen.add(c);list.push(c);}}
 doc.categories=list;return doc;
}
export function addCategory(doc,name) {
 const t=String(name).trim();if(!t||t.length>60)return null;
 normalizeCategories(doc);if(!doc.categories.includes(t))doc.categories.push(t);return t;
}
export function removeCategory(doc,name) {
 normalizeCategories(doc);
 if(doc.pages.some(p=>categoryOf(p)===name))return false;
 doc.categories=doc.categories.filter(c=>c!==name);return true;
}
// Move a page into `category`, placed before page `beforeId` (same category) or at the
// end of that category when beforeId is null.
export function movePage(doc,pageId,category,beforeId=null) {
 const p=doc.pages.find(x=>x.id===pageId);if(!p||beforeId===pageId)return false;
 const rest=doc.pages.filter(x=>x.id!==pageId);p.category=category.trim();
 let index=beforeId?rest.findIndex(x=>x.id===beforeId&&categoryOf(x)===p.category):-1;
 if(index<0){index=rest.length;for(let i=rest.length-1;i>=0;i--)if(categoryOf(rest[i])===p.category){index=i+1;break;}}
 rest.splice(index,0,p);doc.pages=rest;
 if(p.category)addCategory(doc,p.category);return true;
}
export function moveCategory(doc,name,beforeName=null) {
 normalizeCategories(doc);
 if(!doc.categories.includes(name)||name===beforeName)return false;
 const rest=doc.categories.filter(c=>c!==name);
 const index=beforeName?rest.indexOf(beforeName):-1;
 rest.splice(index<0?rest.length:index,0,name);doc.categories=rest;return true;
}
// ---- trash ----
function ensureActive(doc,removedIndex) {
 if(!doc.pages.length)doc.pages.push(newPage('はじめのページ'));
 if(!doc.pages.some(p=>p.id===doc.activeId))doc.activeId=doc.pages[Math.min(Math.max(0,removedIndex),doc.pages.length-1)].id;
}
export function renameCategory(doc,oldName,newName) {
 const next=String(newName).trim();normalizeCategories(doc);
 if(!next||next.length>60||!doc.categories.includes(oldName))return null;
 if(next===oldName)return next;
 for(const p of doc.pages)if(categoryOf(p)===oldName)p.category=next;
 doc.categories=doc.categories.includes(next)?doc.categories.filter(c=>c!==oldName):doc.categories.map(c=>c===oldName?next:c);
 return next;
}
export function deletePage(doc,id) {
 const i=doc.pages.findIndex(p=>p.id===id);if(i<0)return null;
 const [p]=doc.pages.splice(i,1);
 const entry={id:crypto.randomUUID(),kind:'page',name:p.title,pages:[p],deletedAt:Date.now()};
 (doc.trash??=[]).push(entry);ensureActive(doc,i);return entry;
}
export function deleteCategory(doc,name) {
 normalizeCategories(doc);if(!name||!doc.categories.includes(name))return null;
 const first=doc.pages.findIndex(p=>categoryOf(p)===name);
 const pages=doc.pages.filter(p=>categoryOf(p)===name);doc.pages=doc.pages.filter(p=>categoryOf(p)!==name);
 doc.categories=doc.categories.filter(c=>c!==name);
 const entry={id:crypto.randomUUID(),kind:'category',name,pages,deletedAt:Date.now()};
 (doc.trash??=[]).push(entry);ensureActive(doc,first<0?0:first);return entry;
}
export function restoreTrash(doc,entryId) {
 const i=(doc.trash||[]).findIndex(t=>t.id===entryId);if(i<0)return null;
 const [entry]=doc.trash.splice(i,1);
 if(entry.kind==='category')addCategory(doc,entry.name);
 for(const p of entry.pages){
  if(entry.kind==='category')p.category=entry.name;
  if(doc.pages.some(x=>x.id===p.id))p.id=crypto.randomUUID();
  doc.pages.push(p);movePage(doc,p.id,categoryOf(p));
 }
 normalizeCategories(doc);
 if(entry.pages[0])doc.activeId=entry.pages[0].id;
 return entry;
}
export function purgeTrash(doc,entryId) {
 const i=(doc.trash||[]).findIndex(t=>t.id===entryId);if(i<0)return false;
 doc.trash.splice(i,1);return true;
}
export function emptyTrash(doc){const n=(doc.trash||[]).length;doc.trash=[];return n;}
export function validateBackup(doc) {
 const bad=()=>{throw new Error('対応するノートデータではないか、試作品の上限を超えています。');};
 if(!doc||![1,2].includes(doc.version)||!Array.isArray(doc.pages)||doc.pages.length<1||doc.pages.length>500)bad();
 if(doc.categories!==undefined){
  if(!Array.isArray(doc.categories)||doc.categories.length>500)bad();const seen=new Set();
  for(const c of doc.categories){if(typeof c!=='string'||!c.trim()||c.length>60||seen.has(c))bad();seen.add(c);}
 }
 const ids=new Set();let points=0,totalImages=0;
 const checkPage=p=>{
  if(!p||typeof p.id!=='string'||p.id.length>100||ids.has(p.id)||typeof p.title!=='string'||p.title.length>120||
   !Number.isFinite(p.updatedAt)||!Array.isArray(p.strokes)||p.strokes.length>50000)bad();
  if(p.category!==undefined&&(typeof p.category!=='string'||p.category.length>60))bad();
  ids.add(p.id);
  const height=doc.version===1?PAGE_HEIGHT:p.height;
  if(!Number.isFinite(height)||height<760||height>MAX_HEIGHT)bad();
  if(doc.version===1){if(typeof p.text!=='string'||p.text.length>200000)bad();}
  else {
   if(!Array.isArray(p.blocks)||p.blocks.length>1000)bad();const blockIds=new Set();
   for(const o of p.blocks){
    if(!o||typeof o.id!=='string'||o.id.length>100||blockIds.has(o.id)||!['text','image'].includes(o.type)||
     ![o.x,o.y,o.width,o.height].every(Number.isFinite)||o.x<0||o.y<0||o.width<40||o.height<24||
     o.x+o.width>PAGE_WIDTH+.01||o.y+o.height>height+.01)bad();
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
   for(const pt of s.points)if(!Array.isArray(pt)||pt.length!==3||!pt.every(Number.isFinite)||pt[0]<0||pt[0]>PAGE_WIDTH||pt[1]<0||pt[1]>height||pt[2]<0||pt[2]>1)bad();
  }
 };
 for(const p of doc.pages)checkPage(p);
 if(!ids.has(doc.activeId))bad();
 if(doc.trash!==undefined){
  if(!Array.isArray(doc.trash)||doc.trash.length>500)bad();
  for(const t of doc.trash){
   if(!t||typeof t.id!=='string'||t.id.length>100||ids.has(t.id)||!['page','category'].includes(t.kind)||typeof t.name!=='string'||t.name.length>120||
    !Number.isFinite(t.deletedAt)||!Array.isArray(t.pages)||t.pages.length>500||(t.kind==='page'&&t.pages.length!==1))bad();
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

