function FourCore(){
"use strict";
// 14x14 board, corners cut. Players: 0 red (bottom), 1 blue (left), 2 yellow (top), 3 green (right). 4 = dead (grey).
const SZ=14,NSQ=196,P=1,N=2,B=3,R=4,Q=5,K=6,DEAD=4;
const VALID=new Uint8Array(NSQ);
for(let r=0;r<SZ;r++)for(let c=0;c<SZ;c++)VALID[r*SZ+c]=((r<3||r>10)&&(c<3||c>10))?0:1;
const FWD=[[-1,0],[0,1],[1,0],[0,-1]];
const KD=[[-1,0],[1,0],[0,-1],[0,1],[-1,-1],[-1,1],[1,-1],[1,1]];
const ND=[[-2,-1],[-2,1],[2,-1],[2,1],[-1,-2],[-1,2],[1,-2],[1,2]];
const PTS=[0,1,3,5,5,9,0];
const VAL=[0,1,3,3.5,5,9,0];
const LETTER='.PNBRQK',FILES='abcdefghijklmn';
function at(sq,dr,dc){const r=((sq/SZ)|0)+dr,c=sq%SZ+dc;if(r<0||r>=SZ||c<0||c>=SZ)return -1;const s=r*SZ+c;return VALID[s]?s:-1;}
function own(p){return p>>3;}
function sqName(s){return FILES[s%SZ]+(SZ-((s/SZ)|0));}
// back rank layout, from each player's left to right
const LINE=[
  {start:13*SZ+3,axis:1,pawn:-SZ},       // red: row 13, cols 3..10
  {start:3*SZ+0,axis:SZ,pawn:1},          // blue: col 0, rows 3..10
  {start:0*SZ+10,axis:-1,pawn:SZ},        // yellow: row 0, cols 10..3
  {start:10*SZ+13,axis:-SZ,pawn:-1}       // green: col 13, rows 10..3
];
const ORDER=[R,N,B,Q,K,B,N,R];
function promoReached(pl,sq){const r=(sq/SZ)|0,c=sq%SZ;return pl===0?r===6:pl===1?c===7:pl===2?r===7:c===6;}
function startLine(pl,sq){const r=(sq/SZ)|0,c=sq%SZ;return pl===0?r===12:pl===1?c===1:pl===2?r===1:c===12;}

function initial(teams){
  const st={b:new Int8Array(NSQ),prom:new Uint8Array(NSQ),moved:new Uint8Array(NSQ),turn:0,alive:[1,1,1,1],points:[0,0,0,0],lastChk:[-1,-1,-1,-1],kings:[0,0,0,0],teams:!!teams,over:null,ply:0,quiet:0};
  for(let pl=0;pl<4;pl++){
    const L=LINE[pl];
    for(let i=0;i<8;i++){const s=L.start+L.axis*i;st.b[s]=pl*8+ORDER[i];if(ORDER[i]===K)st.kings[pl]=s;st.b[s+L.pawn]=pl*8+P;}
  }
  return st;
}
function clone(st){return {b:st.b.slice(),prom:st.prom.slice(),moved:st.moved.slice(),turn:st.turn,alive:st.alive.slice(),points:st.points.slice(),lastChk:st.lastChk.slice(),kings:st.kings.slice(),teams:st.teams,over:st.over,ply:st.ply,quiet:st.quiet};}
function isOpp(st,a,b){if(a===b)return false;if(st.teams&&(a&1)===(b&1))return false;return true;}
function capturable(st,pl,q){
  if(!q)return false;const o=own(q);
  if((q&7)===K)return false;
  if(o===DEAD)return true;
  return isOpp(st,pl,o);
}
function attackedBy(st,sq,o){
  const b=st.b;
  // pawns of o attack sq from sq - fwd +/- side
  const f=FWD[o];
  for(const s of [-1,1]){const side=f[0]===0?[s,0]:[0,s];const ps=at(sq,-f[0]+side[0],-f[1]+side[1]);if(ps>=0&&b[ps]===o*8+P)return true;}
  for(const d of ND){const s=at(sq,d[0],d[1]);if(s>=0&&b[s]===o*8+N)return true;}
  for(const d of KD){const s=at(sq,d[0],d[1]);if(s>=0&&b[s]===o*8+K)return true;}
  for(let i=0;i<8;i++){
    const d=KD[i],diag=i>=4;let s=at(sq,d[0],d[1]);
    while(s>=0){const q=b[s];if(q){if(own(q)===o){const t=q&7;if(t===Q||(diag?t===B:t===R))return true;}break;}s=at(s,d[0],d[1]);}
  }
  return false;
}
function attacked(st,sq,pl){for(let o=0;o<4;o++)if(st.alive[o]&&isOpp(st,pl,o)&&attackedBy(st,sq,o))return true;return false;}
function inCheck(st,pl){return st.alive[pl]&&attacked(st,st.kings[pl],pl);}
function pseudo(st,pl){
  const b=st.b,out=[];
  for(let sq=0;sq<NSQ;sq++){
    const p=b[sq];if(!p||own(p)!==pl)continue;const t=p&7;
    if(t===P){
      const f=FWD[pl];const s1=at(sq,f[0],f[1]);
      if(s1>=0&&!b[s1]){
        out.push({from:sq,to:s1,promo:promoReached(pl,s1)?Q:0});
        if(startLine(pl,sq)){const s2=at(s1,f[0],f[1]);if(s2>=0&&!b[s2])out.push({from:sq,to:s2,promo:0});}
      }
      for(const s of [-1,1]){const side=f[0]===0?[s,0]:[0,s];const c=at(sq,f[0]+side[0],f[1]+side[1]);if(c>=0&&capturable(st,pl,b[c]))out.push({from:sq,to:c,promo:promoReached(pl,c)?Q:0});}
    }else if(t===N||t===K){
      for(const d of (t===N?ND:KD)){const s=at(sq,d[0],d[1]);if(s<0)continue;const q=b[s];if(!q||capturable(st,pl,q))out.push({from:sq,to:s,promo:0});}
      if(t===K&&!st.moved[sq]&&sq===LINE[pl].start+LINE[pl].axis*4)castles(st,pl,sq,out);
    }else{
      const lo=t===R?0:t===B?4:0,hi=t===B?8:t===R?4:8;
      for(let i=lo;i<hi;i++){const d=KD[i];let s=at(sq,d[0],d[1]);while(s>=0){const q=b[s];if(!q)out.push({from:sq,to:s,promo:0});else{if(capturable(st,pl,q))out.push({from:sq,to:s,promo:0});break;}s=at(s,d[0],d[1]);}}
    }
  }
  return out;
}
function castles(st,pl,ks,out){
  const L=LINE[pl],b=st.b;
  for(const side of [1,-1]){
    const rs=side>0?L.start+L.axis*7:L.start;
    if(b[rs]!==pl*8+R||st.moved[rs])continue;
    let ok=true;
    for(let s=ks+side*L.axis;s!==rs;s+=side*L.axis)if(b[s]){ok=false;break;}
    if(!ok)continue;
    const kd=ks+2*side*L.axis;
    for(let s=ks;;s+=side*L.axis){if(attacked(st,s,pl)){ok=false;break;}if(s===kd)break;}
    if(ok)out.push({from:ks,to:kd,promo:0,castle:{rf:rs,rt:ks+side*L.axis}});
  }
}
// apply a move to a copy; returns the new state with info about what happened
function apply(st,m){
  const n=clone(st),b=n.b,pl=st.turn;
  const p=b[m.from],cap=b[m.to];
  let gained=0;
  if(cap){
    const co=own(cap);
    if(co!==DEAD&&!st.teams)gained=n.prom[m.to]?1:PTS[cap&7];
  }
  b[m.to]=m.promo?pl*8+m.promo:p;n.prom[m.to]=m.promo?1:n.prom[m.from];
  b[m.from]=0;n.prom[m.from]=0;n.moved[m.from]=1;n.moved[m.to]=1;
  if((p&7)===K)n.kings[pl]=m.to;
  if(m.castle){b[m.castle.rt]=b[m.castle.rf];b[m.castle.rf]=0;n.moved[m.castle.rf]=1;}
  n.points[pl]+=gained;
  n.lastMove=[m.from,m.to];n.captured=cap||0;n.gained=gained;
  for(let o=0;o<4;o++)if(o!==pl&&n.alive[o]&&isOpp(n,pl,o)&&attackedBy(n,n.kings[o],pl))n.lastChk[o]=pl;
  n.ply++;n.quiet=(cap||(p&7)===P)?0:st.quiet+1;
  return n;
}
function legal(st,pl){
  if(pl===undefined)pl=st.turn;
  const out=[];
  for(const m of pseudo(st,pl)){const n=apply(st,m);if(!attacked(n,n.kings[pl],pl))out.push(m);}
  return out;
}
function eliminate(st,pl){
  st.alive[pl]=0;
  for(let s=0;s<NSQ;s++){const q=st.b[s];if(q&&own(q)===pl)st.b[s]=DEAD*8+(q&7);}
}
// after a move: pass the turn, and settle any player who has no legal move on their turn
function advance(st){
  const events=[];
  for(let guard=0;guard<4;guard++){
    let nx=st.turn;
    do{nx=(nx+1)%4;}while(!st.alive[nx]&&nx!==st.turn);
    st.turn=nx;
    if(aliveCount(st)<=1)break;
    if(st.teams&&teamDone(st))break;
    const L=legal(st,nx);
    if(L.length)break;
    const chk=attacked(st,st.kings[nx],nx);
    if(st.teams){
      st.over=chk?{loserTeam:nx&1,reason:'Checkmate'}:{draw:true,reason:'Stalemate'};
      events.push({pl:nx,type:chk?'mate':'stalemate'});
      return events;
    }
    if(chk){const by=st.lastChk[nx];if(by>=0&&st.alive[by])st.points[by]+=20;events.push({pl:nx,type:'mate',by});}
    else{st.points[nx]+=20;events.push({pl:nx,type:'stalemate'});}
    eliminate(st,nx);
  }
  checkEnd(st);
  return events;
}
function aliveCount(st){return st.alive.reduce((a,b)=>a+b,0);}
function teamDone(st){return !(st.alive[0]||st.alive[2])||!(st.alive[1]||st.alive[3]);}
function checkEnd(st){
  if(st.over)return;
  if(st.teams&&st.quiet>=100){st.over={draw:true,reason:'25 rounds without a capture or pawn move'};return;}
  if(st.teams){if(teamDone(st))st.over={loserTeam:(st.alive[0]||st.alive[2])?1:0,reason:'Team eliminated'};return;}
  if(st.quiet>=100){st.over=st.teams?{draw:true,reason:'25 rounds without a capture or pawn move'}:{reason:'25 rounds without a capture or pawn move'};return;}
  const alive=[0,1,2,3].filter(p=>st.alive[p]);
  if(alive.length<=1){st.over={reason:'Last player standing'};return;}
  if(alive.length===2){const [a,b]=alive;if(Math.abs(st.points[a]-st.points[b])>=21&&Math.max(st.points[a],st.points[b])===Math.max(...st.points))st.over={reason:'21-point lead with two players left'};}
}
function standings(st){return [0,1,2,3].sort((a,b)=>st.points[b]-st.points[a]||st.alive[b]-st.alive[a]);}
function san(st,m){
  const p=st.b[m.from],t=p&7;let s;
  if(m.castle)s=m.castle.rf===LINE[st.turn].start?'O-O-O':'O-O';
  else{
    const cap=!!st.b[m.to];
    s=(t===P?(cap?FILES[m.from%SZ]:''):LETTER[t])+(cap?'x':'')+sqName(m.to)+(m.promo?'=Q':'');
  }
  const n=apply(st,m);
  for(let o=0;o<4;o++)if(o!==st.turn&&n.alive[o]&&isOpp(n,st.turn,o)&&attackedBy(n,n.kings[o],st.turn)){s+='+';break;}
  return s;
}

/* ---------- bots ---------- */
function risk(st,pl){
  // biggest loss an opponent can inflict next: value of attacked pieces, halved when defended
  let worst=0;const b=st.b;
  for(let s=0;s<NSQ;s++){
    const q=b[s];if(!q||own(q)!==pl)continue;const t=q&7;if(t===K)continue;
    if(!attacked(st,s,pl))continue;
    const v=st.prom[s]?2:VAL[t];
    const defended=defendedBy(st,s,pl);
    const loss=defended?Math.max(0,v-minAttacker(st,s,pl)):v;
    if(loss>worst)worst=loss;
  }
  return worst;
}
function defendedBy(st,s,pl){const q=st.b[s];st.b[s]=DEAD*8+P;const r=attackedBy(st,s,pl);st.b[s]=q;return r;}
function minAttacker(st,sq,pl){
  let best=99;
  for(let o=0;o<4;o++){
    if(!st.alive[o]||!isOpp(st,pl,o))continue;
    for(const m of pseudo(Object.assign({},st,{turn:o}),o))if(m.to===sq){const v=VAL[st.b[m.from]&7]||0.5;if(v<best)best=v;}
  }
  return best===99?0:best;
}
function material(st,pl){let v=0;for(let s=0;s<NSQ;s++){const q=st.b[s];if(q&&own(q)===pl)v+=st.prom[s]?2:VAL[q&7];}return v;}
function positional(st,pl,m){
  const p=st.b[m.from],t=p&7;let v=0;
  const r=(m.to/SZ)|0,c=m.to%SZ,cd=Math.abs(r-6.5)+Math.abs(c-6.5);
  const r0=(m.from/SZ)|0,c0=m.from%SZ,cd0=Math.abs(r0-6.5)+Math.abs(c0-6.5);
  if(t===N||t===B)v+=(cd0-cd)*0.05;
  if(t===P)v+=0.04;
  if(t===K&&!m.castle)v-=0.3;
  if(m.castle)v+=0.4;
  if(t===Q&&st.ply<16)v-=0.15;
  // opening principles for the first ~8 moves each: centre pawns, develop knights and bishops, keep rooks home
  if(st.ply<32){
    if(t===P&&startLine(pl,m.from))v+=(cd0-cd)*0.05+(cd<=7?0.1:0);
    if((t===N||t===B)&&!st.moved[m.from])v+=0.25;
    if(t===R&&!m.castle)v-=0.2;
    if(t===Q)v-=0.1;
  }
  return v;
}
function quickScore(st,m,pl){
  const n=apply(st,m);
  let s=(st.teams?(n.captured&&own(n.captured)!==DEAD?VAL[n.captured&7]:0):n.gained)+(n.captured&&own(n.captured)!==DEAD&&!st.teams?VAL[n.captured&7]*0.3:0);
  s+=positional(st,pl,m);
  // a check that leaves the victim without moves is worth a lot
  for(let o=0;o<4;o++){
    if(o===pl||!n.alive[o]||!isOpp(n,pl,o))continue;
    if(attackedBy(n,n.kings[o],pl)){s+=0.3;if(!legal(Object.assign(clone(n),{turn:o}),o).length)s+=st.teams?100:20;}
  }
  return {n,s};
}
function hardPick(st,pl,L){
  let best=null,bs=-1e9;
  for(const m of L){const r=quickScore(st,m,pl);const sc=r.s-risk(r.n,pl)*0.95+Math.random()*0.05;if(sc>bs){bs=sc;best=r;}}
  return best;
}
function think(st,level){
  const pl=st.turn,L=legal(st,pl);
  if(!L.length)return null;
  const early=st.ply<32;
  if(level==='easy'&&!early&&Math.random()<0.25)return L[(Math.random()*L.length)|0];
  if(level==='impossible'){
    const cands=L.map(m=>{const r=quickScore(st,m,pl);return {m,n:r.n,s:r.s-risk(r.n,pl)*0.95};}).sort((a,b)=>b.s-a.s).slice(0,6);
    const worth=x=>material(x,pl)+(st.teams?0:x.points[pl]);
    let best=cands[0],bf=-1e9;
    for(const c of cands){
      let cur=c.n;
      let o=pl;
      for(let i=0;i<3;i++){
        o=(o+1)%4;if(!cur.alive[o])continue;
        const c2=clone(cur);c2.turn=o;const L2=legal(c2,o);if(!L2.length)continue;
        const r=hardPick(c2,o,L2);if(r)cur=r.n;
      }
      const f=c.s+(worth(cur)-worth(c.n))*0.7-risk(cur,pl)*0.3;
      if(f>bf){bf=f;best=c;}
    }
    return best.m;
  }
  const noise=({easy:3,medium:1.2,hard:0.25}[level]||1)*(early?0.15:1);
  let best=null,bestS=-1e9;
  for(const m of L){
    const {n,s:q}=quickScore(st,m,pl);
    let s=q;
    if(level==='medium')s-=risk(n,pl)*0.6;
    else if(level==='hard')s-=risk(n,pl)*0.95;
    s+=(Math.random()*2-1)*noise;
    if(s>bestS){bestS=s;best=m;}
  }
  return best;
}
return {SZ,NSQ,VALID,initial,clone,apply,legal,advance,eliminate,inCheck,attacked,standings,san,think,sqName,checkEnd,own,DEAD,K,P};
}
