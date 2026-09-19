const DB_NAME='techo-local-v1';
export function openStore(){return new Promise((resolve,reject)=>{
 const r=indexedDB.open(DB_NAME,1);r.onupgradeneeded=()=>r.result.createObjectStore('notebook');
 r.onsuccess=()=>resolve(r.result);r.onerror=()=>reject(r.error);r.onblocked=()=>reject(new Error('別のタブを閉じてください。'));
});}
export function loadNotebook(db,key='current'){return new Promise((resolve,reject)=>{
 const r=db.transaction('notebook','readonly').objectStore('notebook').get(key);
 r.onsuccess=()=>resolve(r.result);r.onerror=()=>reject(r.error);
});}
export function saveNotebook(db,doc){return new Promise((resolve,reject)=>{
 const tx=db.transaction('notebook','readwrite');tx.objectStore('notebook').put(doc,'current');
 tx.oncomplete=()=>resolve();tx.onerror=()=>reject(tx.error);tx.onabort=()=>reject(tx.error||new Error('保存中断'));
});}
export function migrateNotebook(db,original,next){return new Promise((resolve,reject)=>{
 const tx=db.transaction('notebook','readwrite'),store=tx.objectStore('notebook'),r=store.get('before-unified-v2');
 r.onsuccess=()=>{if(r.result===undefined)store.put(original,'before-unified-v2');store.put(next,'current');};
 tx.oncomplete=()=>resolve();tx.onerror=()=>reject(tx.error);tx.onabort=()=>reject(tx.error||new Error('変換中断'));
});}

