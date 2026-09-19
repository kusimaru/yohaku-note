// Local persistence (IndexedDB). Each page and each trash entry is stored under its own key so
// that saving after a pen stroke writes only that page, not the whole notebook:
//   'meta'        {version, activeId, categories, metaUpdatedAt, pageIds, trashIds}
//   'page:<id>'   page object
//   'trash:<id>'  trash entry
// Older installs kept one document under 'current'; it is read as a fallback and replaced by
// the split layout on the first save. 'before-unified-v2' keeps the pre-v2 backup untouched.
const DB_NAME='techo-local-v1';
const PAGE_RANGE=()=>IDBKeyRange.bound('page:','page:￿'),TRASH_RANGE=()=>IDBKeyRange.bound('trash:','trash:￿');
export function openStore(){return new Promise((resolve,reject)=>{
 const r=indexedDB.open(DB_NAME,1);r.onupgradeneeded=()=>r.result.createObjectStore('notebook');
 r.onsuccess=()=>resolve(r.result);r.onerror=()=>reject(r.error);r.onblocked=()=>reject(new Error('別のタブを閉じてください。'));
});}
const request=(store,fn)=>new Promise((resolve,reject)=>{const r=fn(store);r.onsuccess=()=>resolve(r.result);r.onerror=()=>reject(r.error);});
// Returns {doc, legacy} — legacy=true when the notebook came from the old single-document key.
export async function loadNotebook(db) {
 const store=db.transaction('notebook','readonly').objectStore('notebook');
 const meta=await request(store,s=>s.get('meta'));
 if(!meta){const current=await request(store,s=>s.get('current'));return current?{doc:current,legacy:true}:{doc:undefined,legacy:false};}
 const [pages,trash]=await Promise.all([request(store,s=>s.getAll(PAGE_RANGE())),request(store,s=>s.getAll(TRASH_RANGE()))]);
 const byId=new Map(pages.map(p=>[p.id,p])),tById=new Map(trash.map(t=>[t.id,t]));
 const {pageIds=[],trashIds=[],...rest}=meta;
 const doc={...rest,pages:pageIds.map(id=>byId.get(id)).filter(Boolean),trash:trashIds.map(id=>tById.get(id)).filter(Boolean)};
 for(const p of pages)if(!doc.pages.includes(p))doc.pages.push(p); // pages missing from the order list are kept, not lost
 return {doc,legacy:false};
}
export function loadKey(db,key){return new Promise((resolve,reject)=>{
 const r=db.transaction('notebook','readonly').objectStore('notebook').get(key);
 r.onsuccess=()=>resolve(r.result);r.onerror=()=>reject(r.error);
});}
function writeSplit(store,doc,dirty) {
 const {pages,trash=[],...rest}=doc;
 store.put({...rest,pageIds:pages.map(p=>p.id),trashIds:trash.map(t=>t.id)},'meta');
 for(const p of pages)if(!dirty||dirty.pages.has(p.id))store.put(p,'page:'+p.id);
 for(const t of trash)if(!dirty||dirty.trash.has(t.id))store.put(t,'trash:'+t.id);
 const keep=new Set([...pages.map(p=>'page:'+p.id),...trash.map(t=>'trash:'+t.id)]);
 const req=store.getAllKeys();
 req.onsuccess=()=>{for(const k of req.result){const key=String(k);if((key.startsWith('page:')||key.startsWith('trash:'))&&!keep.has(key))store.delete(k);}};
}
// dirty: {pages:Set, trash:Set} to write only those items; null writes everything.
// dropLegacy: remove the old single-document key once the split layout is in place.
export function saveNotebook(db,doc,dirty=null,dropLegacy=false){return new Promise((resolve,reject)=>{
 const tx=db.transaction('notebook','readwrite'),store=tx.objectStore('notebook');
 writeSplit(store,doc,dirty);
 if(dropLegacy)store.delete('current');
 tx.oncomplete=()=>resolve();tx.onerror=()=>reject(tx.error);tx.onabort=()=>reject(tx.error||new Error('保存中断'));
});}
// Version-1 notebooks: keep the original under 'before-unified-v2', store the converted one split.
export function migrateNotebook(db,original,next){return new Promise((resolve,reject)=>{
 const tx=db.transaction('notebook','readwrite'),store=tx.objectStore('notebook'),r=store.get('before-unified-v2');
 r.onsuccess=()=>{if(r.result===undefined)store.put(original,'before-unified-v2');writeSplit(store,next,null);store.delete('current');};
 tx.oncomplete=()=>resolve();tx.onerror=()=>reject(tx.error);tx.onabort=()=>reject(tx.error||new Error('変換中断'));
});}
