// Cloud sync: keeps this device's notebook and the cloud copy the same.
// Rule: the newer copy (by updatedAt) always wins, per page. Pages, trash entries and the
// notebook layout (category order, page order) are synced; the active page is per device.
//
// Storage layout (Firestore):
//   users/{uid}/pages/{pageId}   {updatedAt, title, category, deleted, chunks, rev}
//   users/{uid}/pages/{pageId}/parts/{n}   {d: base64 chunk}
//   users/{uid}/trash/{entryId}  (same shape)
//   users/{uid}/meta/notebook    {categories, order, updatedAt}
// A page is JSON → UTF-8 → base64, split into chunks below Firestore's 1 MiB document limit.

export const SDK_VERSION='10.14.1';
export const FIREBASE_CONFIG={
 apiKey:'AIzaSyD39zOakI_jQFvkSPj03zv9ByPUugXKMew',
 authDomain:'yohaku-note-3c146.firebaseapp.com',
 projectId:'yohaku-note-3c146',
 storageBucket:'yohaku-note-3c146.firebasestorage.app',
 messagingSenderId:'402523531846',
 appId:'1:402523531846:web:84e8fbbbc0f83b3d37f847'
};
const CHUNK_BYTES=600000; // multiple of 3 so every chunk is valid base64 on its own

export function encodeChunks(obj) {
 const bytes=new TextEncoder().encode(JSON.stringify(obj)),out=[];
 for(let i=0;i<bytes.length;i+=CHUNK_BYTES){
  const slice=bytes.subarray(i,i+CHUNK_BYTES);let s='';
  for(let j=0;j<slice.length;j+=8192)s+=String.fromCharCode.apply(null,slice.subarray(j,j+8192));
  out.push(btoa(s));
 }
 return out.length?out:[''];
}
export function decodeChunks(chunks) {
 const parts=chunks.map(c=>{const bin=atob(c),b=new Uint8Array(bin.length);for(let i=0;i<bin.length;i++)b[i]=bin.charCodeAt(i);return b;});
 const all=new Uint8Array(parts.reduce((n,p)=>n+p.length,0));let o=0;
 for(const p of parts){all.set(p,o);o+=p.length;}
 return JSON.parse(new TextDecoder().decode(all));
}
export function describeAuthError(e) {
 const code=e?.code||'';
 if(code.includes('invalid-email'))return 'メールアドレスの形が正しくありません。';
 if(code.includes('missing-password')||code.includes('weak-password'))return 'パスワードは6文字以上にしてください。';
 if(code.includes('email-already-in-use'))return 'このメールアドレスはすでに登録されています。「ログイン」を押してください。';
 if(code.includes('invalid-credential')||code.includes('wrong-password')||code.includes('user-not-found'))return 'メールアドレスかパスワードが違います。初めての場合は「新規登録」を押してください。';
 if(code.includes('too-many-requests'))return '試行回数が多すぎます。しばらく待ってからやり直してください。';
 if(code.includes('network-request-failed'))return 'インターネットに接続できません。';
 if(code.includes('operation-not-allowed'))return 'メール/パスワードでのログインが Firebase 側で有効になっていません。';
 return e?.message||String(e);
}

// ---------- Firebase transport ----------
export async function createFirebaseTransport(config=FIREBASE_CONFIG) {
 const base='https://www.gstatic.com/firebasejs/'+SDK_VERSION+'/';
 const [{initializeApp},A,F]=await Promise.all([import(base+'firebase-app.js'),import(base+'firebase-auth.js'),import(base+'firebase-firestore.js')]);
 const app=initializeApp(config),auth=A.getAuth(app);
 let db;
 try{db=F.initializeFirestore(app,{localCache:F.persistentLocalCache({tabManager:F.persistentMultipleTabManager()})});}
 catch{db=F.getFirestore(app);}
 const ref=(uid,c,id)=>F.doc(db,'users',uid,c,id),parts=(uid,c,id)=>F.collection(db,'users',uid,c,id,'parts');
 return {
  kind:'firebase',
  onAuth(cb){return A.onAuthStateChanged(auth,u=>cb(u?{uid:u.uid,email:u.email||''}:null));},
  signIn:(email,password)=>A.signInWithEmailAndPassword(auth,email,password),
  signUp:(email,password)=>A.createUserWithEmailAndPassword(auth,email,password),
  resetPassword:email=>A.sendPasswordResetEmail(auth,email),
  signOut:()=>A.signOut(auth),
  async write(uid,c,id,obj,meta){
   const chunks=encodeChunks(obj),batch=F.writeBatch(db);
   batch.set(ref(uid,c,id),{...meta,deleted:false,chunks:chunks.length,rev:meta.updatedAt});
   chunks.forEach((d,i)=>batch.set(F.doc(parts(uid,c,id),String(i)),{d}));
   await batch.commit();
   // drop stale parts left by a previous, larger version
   const old=await F.getDocs(parts(uid,c,id));const extra=[];old.forEach(d=>{if(Number(d.id)>=chunks.length)extra.push(d.ref);});
   if(extra.length){const b2=F.writeBatch(db);extra.forEach(r=>b2.delete(r));await b2.commit();}
  },
  async remove(uid,c,id,updatedAt){
   const batch=F.writeBatch(db);batch.set(ref(uid,c,id),{deleted:true,updatedAt,chunks:0,rev:updatedAt});
   const old=await F.getDocs(parts(uid,c,id));old.forEach(d=>batch.delete(d.ref));await batch.commit();
  },
  async read(uid,c,id){
   const meta=await F.getDoc(ref(uid,c,id));if(!meta.exists()||meta.data().deleted)return null;
   const n=meta.data().chunks,snap=await F.getDocsFromServer(parts(uid,c,id)),arr=[];
   snap.forEach(d=>{arr[Number(d.id)]=d.data().d;});
   const chunks=arr.slice(0,n);if(chunks.length!==n||chunks.some(x=>typeof x!=='string'))throw new Error('incomplete');
   return {updatedAt:meta.data().updatedAt,obj:decodeChunks(chunks)};
  },
  listen(uid,c,cb){
   return F.onSnapshot(F.collection(db,'users',uid,c),snap=>{
    cb(snap.docChanges().map(ch=>({type:ch.type,id:ch.doc.id,...ch.doc.data()})),snap.metadata.fromCache);
   },e=>cb(null,false,e));
  },
  writeMeta:(uid,obj)=>F.setDoc(ref(uid,'meta','notebook'),obj),
  listenMeta(uid,cb){return F.onSnapshot(ref(uid,'meta','notebook'),d=>cb(d.exists()?d.data():null),e=>cb(null,e));}
 };
}

// ---------- test transport (same-origin fake cloud served by server.cjs with FAKE_SYNC=1) ----------
export function createFakeTransport(base='/__fake-sync') {
 let user=null;try{user=JSON.parse(localStorage.getItem('yohaku-fake-user')||'null');}catch{}
 const authCbs=[];const notify=()=>authCbs.forEach(cb=>cb(user));
 const api=async(path,body)=>{const r=await fetch(base+path,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body||{})});if(!r.ok)throw new Error('fake sync '+r.status);return r.json();};
 const setUser=u=>{user=u;try{if(u)localStorage.setItem('yohaku-fake-user',JSON.stringify(u));else localStorage.removeItem('yohaku-fake-user');}catch{}notify();};
 const events=(uid,c,cb)=>{const es=new EventSource(base+'/events?uid='+encodeURIComponent(uid)+'&c='+encodeURIComponent(c));es.onmessage=e=>cb(JSON.parse(e.data));return()=>es.close();};
 return {
  kind:'fake',
  onAuth(cb){authCbs.push(cb);setTimeout(()=>cb(user),0);return()=>{const i=authCbs.indexOf(cb);if(i>=0)authCbs.splice(i,1);};},
  async signIn(email,password){if(!email||!password)throw {code:'auth/invalid-email'};setUser({uid:'u-'+email,email});},
  async signUp(email,password){if(!email||password.length<6)throw {code:'auth/weak-password'};setUser({uid:'u-'+email,email});},
  async resetPassword(){},
  async signOut(){setUser(null);},
  write:(uid,c,id,obj,meta)=>api('/write',{uid,c,id,meta:{...meta,deleted:false},chunks:encodeChunks(obj)}),
  remove:(uid,c,id,updatedAt)=>api('/write',{uid,c,id,meta:{deleted:true,updatedAt},chunks:[]}),
  async read(uid,c,id){const r=await api('/read',{uid,c,id});return r.chunks?{updatedAt:r.meta.updatedAt,obj:decodeChunks(r.chunks)}:null;},
  listen:(uid,c,cb)=>events(uid,c,m=>cb(m.changes,false)),
  writeMeta:(uid,obj)=>api('/write',{uid,c:'meta',id:'notebook',meta:obj,chunks:[]}),
  listenMeta:(uid,cb)=>events(uid,'meta',m=>{const nb=m.changes.find(x=>x.id==='notebook');if(nb)cb(nb);})
 };
}

// ---------- engine ----------
// host: {getDoc, setStatus(state,detail), applyPage(id,page|null), applyTrash(id,entry|null),
//        applyNotebook(meta), isBusy(), validatePage(page), validateTrash(entry)}
export function createSyncEngine(transport,host) {
 const pending=new Map();let uid=null,unsubs=[],timer=null,flushing=false,readQueue=[],reading=false,stopped=false;
 const seen={pages:new Set(),trash:new Set()},firstSnapshot={pages:false,trash:false};
 const persist=()=>{try{localStorage.setItem('yohaku-sync-pending',JSON.stringify([...pending.keys()]));}catch{}};
 try{for(const k of JSON.parse(localStorage.getItem('yohaku-sync-pending')||'[]'))pending.set(k,true);}catch{}
 const schedule=(ms=1200)=>{clearTimeout(timer);timer=setTimeout(flush,ms);};
 function mark(kind,id=''){pending.set(kind+':'+id,true);persist();if(uid)schedule();}
 async function flush() {
  if(!uid||flushing||stopped)return;
  if(!pending.size){host.setStatus('online');return;}
  flushing=true;host.setStatus('sending',pending.size);
  try{
   for(const key of [...pending.keys()]){
    const i=key.indexOf(':'),kind=key.slice(0,i),id=key.slice(i+1),doc=host.getDoc();
    if(kind==='page'){
     const p=doc.pages.find(x=>x.id===id);
     if(p)await transport.write(uid,'pages',id,p,{updatedAt:p.updatedAt||Date.now(),title:p.title||'',category:p.category||''});
     else await transport.remove(uid,'pages',id,Date.now());
    } else if(kind==='trash'){
     const e=(doc.trash||[]).find(x=>x.id===id);
     if(e)await transport.write(uid,'trash',id,e,{updatedAt:e.deletedAt||Date.now(),name:e.name||''});
     else await transport.remove(uid,'trash',id,Date.now());
    } else if(kind==='notebook'){
     await transport.writeMeta(uid,{categories:doc.categories||[],order:doc.pages.map(p=>p.id),updatedAt:doc.metaUpdatedAt||Date.now()});
    }
    pending.delete(key);persist();
   }
   host.setStatus('online');
  }catch(e){host.setStatus(navigator.onLine?'error':'offline',pending.size,e);schedule(15000);}
  finally{flushing=false;if(pending.size&&!timer)schedule();}
 }
 function queueRead(c,id,updatedAt){readQueue=readQueue.filter(r=>!(r.c===c&&r.id===id));readQueue.push({c,id,updatedAt});drainReads();}
 async function drainReads() {
  if(reading||!uid)return;reading=true;
  try{
   while(readQueue.length&&!stopped){
    if(host.isBusy()){await new Promise(r=>setTimeout(r,400));continue;}
    const job=readQueue.shift();
    try{
     const got=await transport.read(uid,job.c,job.id);
     if(!got)continue;
     if(job.c==='pages'){const page=got.obj;if(page&&page.id===job.id&&host.validatePage(page))host.applyPage(job.id,page);}
     else {const entry=got.obj;if(entry&&entry.id===job.id&&host.validateTrash(entry))host.applyTrash(job.id,entry);}
    }catch(e){console.warn('sync read failed',job.c,job.id,e);readQueue.push(job);await new Promise(r=>setTimeout(r,3000));if(readQueue.length===1&&readQueue[0]===job){break;}}
   }
  }finally{reading=false;}
 }
 function onChanges(c,changes,fromCache,error) {
  if(error){host.setStatus('error',0,error);return;}
  const doc=host.getDoc(),list=c==='pages'?doc.pages:(doc.trash||[]),stamp=c==='pages'?(x=>x.updatedAt||0):(x=>x.deletedAt||0),prefix=c==='pages'?'page:':'trash:';
  for(const ch of changes||[]){
   if(ch.type==='removed')continue;
   seen[c].add(ch.id);
   const local=list.find(x=>x.id===ch.id),localStamp=local?stamp(local):-1,remoteStamp=ch.updatedAt||0,pendingLocal=pending.has(prefix+ch.id);
   if(ch.deleted){
    if(local&&localStamp>remoteStamp){mark(c==='pages'?'page':'trash',ch.id);continue;}
    if(local&&!pendingLocal)(c==='pages'?host.applyPage:host.applyTrash)(ch.id,null);
    continue;
   }
   if(local&&localStamp>=remoteStamp)continue;
   if(pendingLocal&&local)continue;
   queueRead(c,ch.id,remoteStamp);
  }
  if(!firstSnapshot[c]&&!fromCache){
   firstSnapshot[c]=true;
   for(const x of list)if(!seen[c].has(x.id))mark(c==='pages'?'page':'trash',x.id);
   if(c==='pages'&&!pending.has('notebook:'))mark('notebook');
  }
 }
 function onMeta(meta,error) {
  if(error){host.setStatus('error',0,error);return;}
  if(!meta)return;const doc=host.getDoc();
  if((meta.updatedAt||0)>(doc.metaUpdatedAt||0)&&!pending.has('notebook:'))host.applyNotebook(meta);
 }
 return {
  markPage:id=>mark('page',id),markTrash:id=>mark('trash',id),markNotebook:()=>mark('notebook'),
  removePage:id=>mark('page',id),removeTrash:id=>mark('trash',id),
  pendingCount:()=>pending.size,
  start(userId){
   this.stop();stopped=false;uid=userId;host.setStatus('connecting');
   firstSnapshot.pages=false;firstSnapshot.trash=false;seen.pages.clear();seen.trash.clear();
   unsubs=[transport.listen(uid,'pages',(ch,fc,e)=>onChanges('pages',ch,fc,e)),transport.listen(uid,'trash',(ch,fc,e)=>onChanges('trash',ch,fc,e)),transport.listenMeta(uid,onMeta)];
   if(pending.size)schedule(500);else host.setStatus('online');
  },
  stop(){stopped=true;for(const u of unsubs)try{u();}catch{}unsubs=[];uid=null;clearTimeout(timer);timer=null;readQueue=[];},
  flushNow(){clearTimeout(timer);timer=null;return flush();},
  retry(){if(uid)schedule(200);}
 };
}
