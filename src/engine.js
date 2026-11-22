function ChessCore(){
"use strict";
const P=1,N=2,B=3,R=4,Q=5,K=6,BL=8,DUCK=16;
const F_EP=1,F_CASTLE=2,F_DOUBLE=4,F_DROP=8;
const NO=[-33,-31,-18,-14,14,18,31,33],KO=[-17,-16,-15,-1,1,15,16,17],BO=[-17,-15,15,17],RO=[-16,-1,1,16];
const VAL=[0,100,320,330,500,900,0];
const ALF=[-34,-30,30,34];
const MATE=30000,INF=32000;
let seed=0x2545F491;
function rnd(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed|0;}
const Z1=new Int32Array(17*128),Z2=new Int32Array(17*128);
for(let i=0;i<Z1.length;i++){Z1[i]=rnd();Z2[i]=rnd();}
const ZC1=new Int32Array(16),ZC2=new Int32Array(16);for(let i=0;i<16;i++){ZC1[i]=rnd();ZC2[i]=rnd();}
const ZE1=new Int32Array(128),ZE2=new Int32Array(128);for(let i=0;i<128;i++){ZE1[i]=rnd();ZE2[i]=rnd();}
const ZP1=new Int32Array(16*64),ZP2=new Int32Array(16*64);for(let i=0;i<ZP1.length;i++){ZP1[i]=rnd();ZP2[i]=rnd();}
const ZK1=new Int32Array(16),ZK2=new Int32Array(16);for(let i=0;i<16;i++){ZK1[i]=rnd();ZK2[i]=rnd();}
const ZS1=rnd(),ZS2=rnd();
const ZQ1=new Int32Array(256),ZQ2=new Int32Array(256);for(let i=0;i<256;i++){ZQ1[i]=rnd();ZQ2[i]=rnd();}
const ZR1=new Int32Array(256),ZR2=new Int32Array(256);for(let i=0;i<256;i++){ZR1[i]=rnd();ZR2[i]=rnd();}
const FILES='abcdefgh',PCH='.pnbrqk';
function sqName(s){return FILES[s&7]+(8-(s>>4));}
function nameSq(n){return (8-(+n[1]))*16+(n.charCodeAt(0)-97);}
const START='rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';

const VARIANTS={
  standard:{checks:true,insuf:true},
  chess960:{checks:true,c960:true,insuf:true},
  crazyhouse:{checks:true,zh:true,no50:true},
  kingofthehill:{checks:true,koth:true},
  threecheck:{checks:true,three:true},
  antichess:{anti:true,fen:'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w - - 0 1'},
  atomic:{checks:true,atomic:true},
  horde:{checks:true,horde:true,fen:'rnbqkbnr/pppppppp/8/1PP2PP1/PPPPPPPP/PPPPPPPP/PPPPPPPP/PPPPPPPP w kq - 0 1'},
  racingkings:{checks:true,racing:true,fen:'8/8/8/8/8/8/krbnNBRK/qrbnNBRQ w - - 0 1'},
  fog:{kingCap:true,fog:true},
  kingcapture:{kingCap:true},
  chaturanga:{checks:true,anc:true,alfil:true,bare:true,fen:'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w - - 0 1'},
  shatranj:{checks:true,anc:true,alfil:true,bare:true,staleWin:true,fen:'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w - - 0 1'},
  makruk:{checks:true,anc:true,khon:true,makruk:true,fen:'rnbqkbnr/8/pppppppp/8/8/PPPPPPPP/8/RNBKQBNR w - - 0 1'},
  duck:{kingCap:true,duck:true},
  torpedo:{checks:true,torpedo:true,insuf:true},
  crazy960:{checks:true,zh:true,c960:true,no50:true},
  bughouse:{checks:true,zh:true,bh:true,no50:true},
  checkless:{checks:true,checkless:true,insuf:true},
  secret:{checks:true,secret:true,insuf:true},
  progressive:{checks:true,prog:true,insuf:true},
  chatgpt:{checks:true,gpt:true},
  setup:{checks:true,setup:true,insuf:true,fen:'8/8/8/8/8/8/8/8[KQRRBBNNPPPPPPPPkqrrbbnnpppppppp] w - - 0 1'}
};
function startFen(v){
  if(VARIANTS[v].c960){
    const r=Array(8).fill('');const free=()=>r.map((x,i)=>x?-1:i).filter(i=>i>=0);
    const pick=a=>a[(Math.random()*a.length)|0];
    r[pick([0,2,4,6])]='b';r[pick([1,3,5,7])]='b';
    r[pick(free())]='q';r[pick(free())]='n';r[pick(free())]='n';
    const f=free();r[f[0]]='r';r[f[1]]='k';r[f[2]]='r';
    const row=r.join('');
    return row+'/pppppppp/8/8/8/8/PPPPPPPP/'+row.toUpperCase()+' w KQkq - 0 1';
  }
  return VARIANTS[v].fen||START;
}
const CENTER=new Uint8Array(128);CENTER[51]=CENTER[52]=CENTER[67]=CENTER[68]=1;
function pf1(s,l){return Math.imul(s*257+l,0x9E3779B1)^0x2c1b3c6d;}
function pf2(s,l){return Math.imul(s*263+l,0x85EBCA6B)^0x297a2d39;}
function adjacent(a,b){return Math.abs((a>>4)-(b>>4))<=1&&Math.abs((a&7)-(b&7))<=1;}

class Pos{
  constructor(variant){
    this.variant=variant||'standard';this.v=VARIANTS[this.variant];
    this.b=new Int8Array(128);this.prom=new Uint8Array(128);this.pock=new Int8Array(16);
    this.turn=0;this.castle=0;this.ep=-1;this.half=0;this.full=1;this.kings=[-1,-1];this.chk=[0,0];this.duck=-1;this.sec=[-1,-1];this.pend=[-1,-1];this.seq=1;this.left=1;
    this.crook=[-1,-1,-1,-1];this.CM=new Int8Array(128).fill(15);
    this.h1=0;this.h2=0;this.hist=[];this.u=[];this.dk=[];
  }
  load(fen){
    const f=fen.trim().split(/\s+/);const b=this.b;b.fill(0);this.prom.fill(0);this.pock.fill(0);
    this.kings=[-1,-1];this.chk=[0,0];this.duck=-1;this.sec=[-1,-1];this.pend=[-1,-1];this.seq=1;this.left=1;
    let r=0,c=0,boardPart=f[0];
    const pk=boardPart.match(/\[([A-Za-z]*)\]$/);
    if(pk){boardPart=boardPart.slice(0,pk.index);for(const ch of pk[1]){const lo=ch.toLowerCase(),t=PCH.indexOf(lo);if(t>0&&t<7)this.pock[(ch===lo?8:0)+t]++;}}
    for(const ch of boardPart){
      if(ch==='/'){r++;c=0;}
      else if(ch>='1'&&ch<='8')c+=+ch;
      else if(ch==='~'){this.prom[r*16+c-1]=1;}
      else{const lo=ch.toLowerCase(),t=PCH.indexOf(lo),blk=ch===lo;const sq=r*16+c;b[sq]=t|(blk?BL:0);if(t===K&&!this.v.anti)this.kings[blk?1:0]=sq;c++;}
    }
    this.turn=f[1]==='b'?1:0;
    this.castle=0;this.crook=[-1,-1,-1,-1];this.CM.fill(15);
    for(const ch of (f[2]||'-')){
      if(ch==='-')continue;
      const col=ch===ch.toUpperCase()?0:1,base=col?0:112,ks=this.kings[col];
      if(ks<0||(ks&0x70)!==base)continue;
      const L=ch.toLowerCase(),rk=R|(col?BL:0);let rf=-1;
      if(L==='k'){for(let x=7;x>(ks&7);x--)if(b[base+x]===rk){rf=base+x;break;}}
      else if(L==='q'){for(let x=0;x<(ks&7);x++)if(b[base+x]===rk){rf=base+x;break;}}
      else{rf=base+(L.charCodeAt(0)-97);if(b[rf]!==rk)rf=-1;}
      if(rf<0)continue;
      const idx=col*2+((rf&7)>(ks&7)?0:1);this.crook[idx]=rf;this.castle|=1<<idx;
    }
    for(let i=0;i<4;i++)if(this.crook[i]>=0)this.CM[this.crook[i]]&=~(1<<i);
    for(let col=0;col<2;col++)if(this.kings[col]>=0&&((this.kings[col]&0x70)===(col?0:112)))this.CM[this.kings[col]]&=col?~12:~3;
    this.ep=(f[3]&&f[3]!=='-')?nameSq(f[3]):-1;
    this.half=+(f[4]||0);this.full=+(f[5]||1);
    this.rehash();this.hist=[this.h1];this.u=[];this.dk=[];return this;
  }
  rehash(){
    let h1=0,h2=0;const b=this.b;
    for(let s=0;s<128;s++){if(s&0x88)continue;const p=b[s];if(p){h1^=Z1[p*128+s];h2^=Z2[p*128+s];}}
    h1^=ZC1[this.castle];h2^=ZC2[this.castle];
    if(this.ep>=0){h1^=ZE1[this.ep];h2^=ZE2[this.ep];}
    if(this.turn){h1^=ZS1;h2^=ZS2;}
    if(this.v.prog){h1^=pf1(this.seq,this.left);h2^=pf2(this.seq,this.left);}
    for(let i=0;i<16;i++){h1^=ZP1[i*64+this.pock[i]];h2^=ZP2[i*64+this.pock[i]];}
    for(let c=0;c<2;c++){h1^=ZK1[c*8+this.chk[c]];h2^=ZK2[c*8+this.chk[c]];if(this.sec[c]>=0){h1^=ZQ1[c*128+this.sec[c]];h2^=ZQ2[c*128+this.sec[c]];}if(this.pend[c]>=0){h1^=ZR1[c*128+this.pend[c]];h2^=ZR2[c*128+this.pend[c]];}}
    this.h1=h1;this.h2=h2;
  }
  setSec(c,sq){if(this.sec[c]>=0){this.h1^=ZQ1[c*128+this.sec[c]];this.h2^=ZQ2[c*128+this.sec[c]];}this.sec[c]=sq;if(sq>=0){this.h1^=ZQ1[c*128+sq];this.h2^=ZQ2[c*128+sq];}}
  setPend(c,sq){if(this.pend[c]>=0){this.h1^=ZR1[c*128+this.pend[c]];this.h2^=ZR2[c*128+this.pend[c]];}this.pend[c]=sq;if(sq>=0){this.h1^=ZR1[c*128+sq];this.h2^=ZR2[c*128+sq];}}
  setPending(a){this.setPend(0,a[0]);this.setPend(1,a[1]);this.hist[this.hist.length-1]=this.h1;}
  // would the opponent's waiting secret queen attack this side's king once it appears?
  secretThreat(side){const o=side^1,ps=this.pend[o];if(ps<0||this.kings[side]<0||this.b[ps]!==(P|(o?BL:0)))return false;this.b[ps]=Q|(o?BL:0);const r=this.attacked(this.kings[side],o);this.b[ps]=P|(o?BL:0);return r;}
  setSecret(a){this.setSec(0,a[0]);this.setSec(1,a[1]);this.hist[this.hist.length-1]=this.h1;}
  x(p,s){this.h1^=Z1[p*128+s];this.h2^=Z2[p*128+s];}
  pockAdd(c,t,d){const i=c*8+t;this.h1^=ZP1[i*64+this.pock[i]];this.h2^=ZP2[i*64+this.pock[i]];this.pock[i]+=d;this.h1^=ZP1[i*64+this.pock[i]];this.h2^=ZP2[i*64+this.pock[i]];}
  fen(){
    let s='';const b=this.b;
    for(let r=0;r<8;r++){
      let e=0;
      for(let c=0;c<8;c++){const p=b[r*16+c];if(!p||p===DUCK){e++;continue;}if(e){s+=e;e=0;}const ch=PCH[p&7];s+=(p&BL)?ch:ch.toUpperCase();if(this.v.zh&&this.prom[r*16+c])s+='~';}
      if(e)s+=e;if(r<7)s+='/';
    }
    if(this.v.zh||this.v.setup){let h='';for(let c=0;c<2;c++)for(let t=6;t>=1;t--)for(let n=0;n<this.pock[c*8+t];n++)h+=c?PCH[t]:PCH[t].toUpperCase();s+='['+h+']';}
    const cs=(this.castle&1?'K':'')+(this.castle&2?'Q':'')+(this.castle&4?'k':'')+(this.castle&8?'q':'');
    return s+' '+(this.turn?'b':'w')+' '+(cs||'-')+' '+(this.ep>=0?sqName(this.ep):'-')+' '+this.half+' '+this.full;
  }
  attacked(sq,by){
    const b=this.b,bb=by?BL:0;let t;
    if(by===0){t=sq+15;if(!(t&0x88)&&b[t]===P)return true;t=sq+17;if(!(t&0x88)&&b[t]===P)return true;}
    else{t=sq-15;if(!(t&0x88)&&b[t]===(P|BL))return true;t=sq-17;if(!(t&0x88)&&b[t]===(P|BL))return true;}
    if(this.v.anc)return this.attackedAnc(sq,by);
    const kn=N|bb,kg=this.v.atomic?-1:(K|bb),bi=B|bb,rk=R|bb,qn=Q|bb;
    for(let i=0;i<8;i++){t=sq+NO[i];if(!(t&0x88)&&b[t]===kn)return true;t=sq+KO[i];if(!(t&0x88)&&b[t]===kg)return true;}
    for(let i=0;i<4;i++){
      let d=BO[i];t=sq+d;
      while(!(t&0x88)){const p=b[t];if(p){if(p===bi||p===qn)return true;break;}t+=d;}
      d=RO[i];t=sq+d;
      while(!(t&0x88)){const p=b[t];if(p){if(p===rk||p===qn)return true;break;}t+=d;}
    }
    return false;
  }
  attackedAnc(sq,by){
    const b=this.b,bb=by?BL:0;let t;
    for(let i=0;i<8;i++){t=sq+NO[i];if(!(t&0x88)&&b[t]===(N|bb))return true;t=sq+KO[i];if(!(t&0x88)&&b[t]===(K|bb))return true;}
    for(let i=0;i<4;i++){t=sq+BO[i];if(!(t&0x88)&&(b[t]===(Q|bb)||(this.v.khon&&b[t]===(B|bb))))return true;}
    if(this.v.alfil)for(const d of ALF){t=sq+d;if(!(t&0x88)&&b[t]===(B|bb))return true;}
    if(this.v.khon){t=sq-(by?16:-16);if(!(t&0x88)&&b[t]===(B|bb))return true;}
    for(let i=0;i<4;i++){const d=RO[i];t=sq+d;while(!(t&0x88)){const p=b[t];if(p){if(p===(R|bb))return true;break;}t+=d;}}
    return false;
  }
  inCheck(side){
    const v=this.v;if(!v.checks)return false;
    const k=this.kings[side];if(k<0)return false;
    if(v.atomic){const ek=this.kings[side^1];if(ek>=0&&adjacent(k,ek))return false;}
    return this.attacked(k,side^1);
  }
  okAfter(us){
    const v=this.v;
    if(v.anti||v.kingCap)return true;
    const k=this.kings[us];
    if(v.atomic){
      if(k<0)return false;
      const ek=this.kings[us^1];if(ek<0)return true;
      if(adjacent(k,ek))return true;
      return !this.attacked(k,us^1);
    }
    if(v.setup){const ek=this.kings[us^1];if(ek>=0&&this.attacked(ek,us))return false;}
    if(k<0)return true;
    if(this.attacked(k,us^1))return false;
    if(v.checkless){const ek=this.kings[us^1];if(ek>=0&&this.attacked(ek,us)&&this.hasEscape(us^1))return false;}
    if(v.racing){const ek=this.kings[us^1];if(ek>=0&&this.attacked(ek,us))return false;}
    return true;
  }
  isCap(m){const fl=(m>>>17)&15;if(fl&F_EP)return true;if(fl&(F_CASTLE|F_DROP))return false;const q=this.b[(m>>7)&127];return q!==0&&q!==DUCK;}
  castleTargets(m){const us=this.turn,kf=m&127,rf=(m>>7)&127,base=us?0:112,side=(rf&7)>(kf&7)?0:1;return [base+(side?2:6),base+(side?3:5)];}
  inSetup(){if(!this.v.setup)return false;for(let i=1;i<16;i++)if(this.pock[i])return true;return false;}
  gen(caps){
    const out=[],b=this.b,us=this.turn,them=us^1,v=this.v;
    if(v.setup&&this.inSetup()){
      if(caps)return out;
      const rows=us?[0,1]:[6,7];
      for(let t=1;t<=6;t++){if(!this.pock[us*8+t])continue;for(const r of rows)for(let f=0;f<8;f++){const sq=r*16+f;if(!b[sq])out.push(t|sq<<7|F_DROP<<17);}}
      return out;
    }
    const promos=v.anti?[Q,R,B,N,K]:v.anc?[Q]:[Q,N,R,B];
    for(let sq=0;sq<120;sq++){
      if(sq&0x88){sq+=7;continue;}
      const p=b[sq];if(!p||(p>>3)!==us)continue;
      const t=p&7;
      if(t===P&&v.secret&&sq===this.sec[us]){
        // the hidden queen: moves like a queen, but may not take the king while hidden
        for(let i=0;i<8;i++){const d=KO[i];let t2=sq+d;while(!(t2&0x88)){const q=b[t2];if(!q){if(!caps)out.push(sq|t2<<7);}else{if((q>>3)===them&&(q&7)!==K)out.push(sq|t2<<7);break;}t2+=d;}}
        continue;
      }
      if(t===P){
        const d=us?16:-16,promR=v.makruk?(us?5:2):(us?7:0),row=sq>>4;
        const t1=sq+d;
        if(!(t1&0x88)&&!b[t1]){
          if((t1>>4)===promR){out.push(sq|t1<<7|Q<<14);if(!caps)for(let i=1;i<promos.length;i++)out.push(sq|t1<<7|promos[i]<<14);}
          else if(!caps){
            out.push(sq|t1<<7);
            const dbl=!v.anc&&(row===(us?1:6)||v.torpedo||(v.horde&&us===0&&row===7));
            const t2=t1+d;
            if(dbl&&!(t2&0x88)&&!b[t2]){
              if((t2>>4)===promR){for(const pp of promos)out.push(sq|t2<<7|pp<<14);}
              else out.push(sq|t2<<7|F_DOUBLE<<17);
            }
          }
        }
        for(let k=-1;k<=1;k+=2){
          const t2=t1+k;if(t2&0x88)continue;const q=b[t2];
          if(q&&(q>>3)===them){
            if((t2>>4)===promR){out.push(sq|t2<<7|Q<<14);if(!caps)for(let i=1;i<promos.length;i++)out.push(sq|t2<<7|promos[i]<<14);}
            else out.push(sq|t2<<7);
          }else if(t2===this.ep&&!q)out.push(sq|t2<<7|F_EP<<17);
        }
      }else if(v.anc&&(t===Q||t===B)){
        const offs=t===Q?BO:v.khon?[-17,-15,15,17,us?16:-16]:ALF;
        for(const o of offs){const t2=sq+o;if(t2&0x88)continue;const q=b[t2];if(!q){if(!caps)out.push(sq|t2<<7);}else if((q>>3)===them)out.push(sq|t2<<7);}
      }else if(t===N||t===K){
        const offs=t===N?NO:KO,noCap=t===K&&v.atomic;
        for(let i=0;i<8;i++){const t2=sq+offs[i];if(t2&0x88)continue;const q=b[t2];if(!q){if(!caps)out.push(sq|t2<<7);}else if((q>>3)===them&&!noCap)out.push(sq|t2<<7);}
        if(t===K&&!caps&&this.castle)this.genCastle(out,sq);
      }else{
        const dirs=t===B?BO:t===R?RO:KO;
        for(let i=0;i<dirs.length;i++){
          const d=dirs[i];let t2=sq+d;
          while(!(t2&0x88)){const q=b[t2];if(!q){if(!caps)out.push(sq|t2<<7);}else{if((q>>3)===them)out.push(sq|t2<<7);break;}t2+=d;}
        }
      }
    }
    if(v.zh&&!caps){
      for(let t=1;t<=5;t++){
        if(!this.pock[us*8+t])continue;
        for(let sq=0;sq<120;sq++){
          if(sq&0x88){sq+=7;continue;}
          if(b[sq])continue;
          if(t===P&&((sq>>4)===0||(sq>>4)===7))continue;
          out.push(t|sq<<7|F_DROP<<17);
        }
      }
    }
    return out;
  }
  genCastle(out,kf){
    const us=this.turn,them=us^1,b=this.b,base=us?0:112,rk=R|(us?BL:0);
    if((kf&0x70)!==base)return;
    for(let side=0;side<2;side++){
      const idx=us*2+side;if(!(this.castle&(1<<idx)))continue;
      const rf=this.crook[idx];if(rf<0||b[rf]!==rk)continue;
      const kd=base+(side?2:6),rd=base+(side?3:5);
      const lo=Math.min(kf,rf,kd,rd),hi=Math.max(kf,rf,kd,rd);
      let ok=true;
      for(let s=lo;s<=hi;s++)if(s!==kf&&s!==rf&&b[s]){ok=false;break;}
      if(!ok)continue;
      if(this.v.checks){
        const a=Math.min(kf,kd),z=Math.max(kf,kd);
        for(let s=a;s<=z;s++)if(this.attacked(s,them)){ok=false;break;}
        if(!ok)continue;
      }
      out.push(kf|rf<<7|F_CASTLE<<17);
    }
  }
  make(m){
    const v=this.v,b=this.b,us=this.turn,them=us^1,ub=us?BL:0;
    const to=(m>>7)&127,fl=(m>>>17)&15,dk=(m>>>21)&127;
    const u={m,p:0,cap:0,capSq:-1,castle:this.castle,ep:this.ep,half:this.half,h1:this.h1,h2:this.h2,k0:this.kings[0],k1:this.kings[1],c0:this.chk[0],c1:this.chk[1],s0:this.sec[0],s1:this.sec[1],q0:this.pend[0],q1:this.pend[1],tr:-1,sq:this.seq,lf:this.left,kt:false,duck:this.duck,pf:0,pc:0,ex:null};
    this.u.push(u);
    this.h1^=ZC1[this.castle];this.h2^=ZC2[this.castle];
    if(this.ep>=0){this.h1^=ZE1[this.ep];this.h2^=ZE2[this.ep];}
    let newEp=-1;
    if(fl&F_DROP){
      const t=m&127,p=t|ub;b[to]=p;this.x(p,to);this.pockAdd(us,t,-1);this.prom[to]=0;this.half=v.setup?0:this.half+1;if(t===K)this.kings[us]=to;
    }else if(fl&F_CASTLE){
      const kf=m&127,rf=to,base=us?0:112,side=(rf&7)>(kf&7)?0:1,kd=base+(side?2:6),rd=base+(side?3:5);
      this.x(K|ub,kf);this.x(R|ub,rf);b[kf]=0;b[rf]=0;b[kd]=K|ub;b[rd]=R|ub;this.x(K|ub,kd);this.x(R|ub,rd);
      this.kings[us]=kd;this.castle&=us?~12:~3;this.half++;
    }else{
      const from=m&127,p=b[from],pr=(m>>14)&7;u.p=p;
      let capSq=to;if(fl&F_EP)capSq=to+(us?-16:16);
      const cap=b[capSq];
      if(v.zh){u.pf=this.prom[from];u.pc=this.prom[capSq];}
      this.x(p,from);b[from]=0;
      if(v.secret&&cap&&capSq===this.sec[them])this.setSec(them,-1);
      if(v.secret&&cap&&capSq===this.pend[them])this.setPend(them,-1);
      if(cap){
        u.cap=cap;u.capSq=capSq;this.x(cap,capSq);b[capSq]=0;
        if(v.zh){if(!v.bh)this.pockAdd(us,u.pc?P:(cap&7),1);this.prom[capSq]=0;}
        if((cap&7)===K&&!v.anti)this.kings[them]=-1;
      }
      if(v.atomic&&cap){
        const ex=[];
        for(let i=0;i<8;i++){
          const s=to+KO[i];if(s&0x88)continue;const q=b[s];
          if(q&&(q&7)!==P){ex.push(s,q);this.x(q,s);b[s]=0;if((q&7)===K)this.kings[q>>3]=-1;this.castle&=this.CM[s];}
        }
        u.ex=ex;
        if((p&7)===K)this.kings[us]=-1;
      }else{
        const wasSec=v.secret&&from===this.sec[us]&&(p&7)===P;
        const np=pr?(pr|ub):p;
        if(wasSec){this.setSec(us,-1);if(!pr)this.setPend(us,to);}
        b[to]=np;this.x(np,to);
        if(v.zh){this.prom[to]=pr?1:u.pf;this.prom[from]=0;}
        if((p&7)===K&&!v.anti)this.kings[us]=to;
      }
      this.castle&=this.CM[from]&this.CM[to];
      this.half=((p&7)===P||cap)?0:this.half+1;
      if((fl&F_DOUBLE)&&b[to]===(P|ub))newEp=(from+to)>>1;
    }
    this.ep=newEp;
    if(newEp>=0){this.h1^=ZE1[newEp];this.h2^=ZE2[newEp];}
    this.h1^=ZC1[this.castle];this.h2^=ZC2[this.castle];
    if(dk){const d=dk-1;if(this.duck>=0){this.x(DUCK,this.duck);b[this.duck]=0;}b[d]=DUCK;this.x(DUCK,d);this.duck=d;}
    if(v.prog){
      // 1, 2, 3 moves: a check ends the series and the count restarts at 1
      const chk=this.kings[them]>=0&&this.attacked(this.kings[them],us);
      this.h1^=pf1(this.seq,this.left);this.h2^=pf2(this.seq,this.left);
      if(chk||this.left<=1){this.seq=chk?1:this.seq+1;this.left=this.seq;}
      else{this.left--;u.kt=true;if(this.ep>=0){this.h1^=ZE1[this.ep];this.h2^=ZE2[this.ep];this.ep=-1;}}
      this.h1^=pf1(this.seq,this.left);this.h2^=pf2(this.seq,this.left);
      if(u.kt){this.hist.push(this.h1);return;}
    }
    if(us===1)this.full++;
    this.turn=them;this.h1^=ZS1;this.h2^=ZS2;
    if(v.secret&&this.pend[them]>=0){const ps=this.pend[them],pw=P|(them?BL:0);if(b[ps]===pw){this.x(pw,ps);b[ps]=Q|(them?BL:0);this.x(b[ps],ps);u.tr=ps;}this.setPend(them,-1);}
    if(v.three){const ek=this.kings[them];if(ek>=0&&this.attacked(ek,us)){const i=us*8+this.chk[us];this.h1^=ZK1[i];this.h2^=ZK2[i];this.chk[us]++;this.h1^=ZK1[i+1];this.h2^=ZK2[i+1];}}
    this.hist.push(this.h1);
  }
  unmake(){
    const u=this.u.pop(),m=u.m,b=this.b;
    if(u.tr>=0)b[u.tr]=P|(this.turn?BL:0);
    const us=u.kt?this.turn:this.turn^1;if(!u.kt){this.turn=us;if(us===1)this.full--;}
    this.seq=u.sq;this.left=u.lf;
    const ub=us?BL:0,to=(m>>7)&127,fl=(m>>>17)&15,dk=(m>>>21)&127;
    if(dk){b[this.duck]=0;if(u.duck>=0)b[u.duck]=DUCK;}
    this.duck=u.duck;
    if(fl&F_DROP){b[to]=0;this.pock[us*8+(m&127)]++;}
    else if(fl&F_CASTLE){
      const kf=m&127,rf=to,base=us?0:112,side=(rf&7)>(kf&7)?0:1;
      b[base+(side?2:6)]=0;b[base+(side?3:5)]=0;b[kf]=K|ub;b[rf]=R|ub;
    }else{
      const from=m&127;
      b[to]=0;b[from]=u.p;
      if(u.ex){const ex=u.ex;for(let i=0;i<ex.length;i+=2)b[ex[i]]=ex[i+1];}
      if(u.cap){b[u.capSq]=u.cap;if(this.v.zh&&!this.v.bh)this.pock[us*8+(u.pc?P:(u.cap&7))]--;}
      if(this.v.zh){this.prom[from]=u.pf;this.prom[to]=0;if(u.cap)this.prom[u.capSq]=u.pc;}
    }
    this.castle=u.castle;this.ep=u.ep;this.half=u.half;this.h1=u.h1;this.h2=u.h2;
    this.kings[0]=u.k0;this.kings[1]=u.k1;this.chk[0]=u.c0;this.chk[1]=u.c1;this.sec[0]=u.s0;this.sec[1]=u.s1;this.pend[0]=u.q0;this.pend[1]=u.q1;
    this.hist.pop();
  }
  makeNull(){
    this.dk.push(this.ep,this.h1,this.h2,this.half);
    this.h1^=ZS1;this.h2^=ZS2;
    if(this.ep>=0){this.h1^=ZE1[this.ep];this.h2^=ZE2[this.ep];}
    this.ep=-1;this.turn^=1;this.half++;this.hist.push(this.h1);
  }
  unmakeNull(){const d=this.dk;this.half=d.pop();this.h2=d.pop();this.h1=d.pop();this.ep=d.pop();this.turn^=1;this.hist.pop();}
  hasEscape(side){
    const t=this.turn;this.turn=side;const ms=this.gen(false);let ok=false;
    for(const m of ms){this.make(m);if(!this.attacked(this.kings[side],side^1))ok=true;this.unmake();if(ok)break;}
    this.turn=t;return ok;
  }
  legal(){
    const ms=this.gen(false),us=this.turn;let out=[];
    for(const m of ms){this.make(m);if(this.okAfter(us))out.push(m);this.unmake();}
    if(this.v.anti){const c=out.filter(m=>this.isCap(m));if(c.length)out=c;}
    return out;
  }
  // duck squares the engine considers after a piece move (opponent to move)
  duckCands(n){
    const b=this.b,me=this.turn^1,res=[];
    const add=s=>{if(s>=0&&!(s&0x88)&&!b[s]&&s!==this.duck&&!res.includes(s))res.push(s);};
    const caps=this.gen(true);let best=-1,bestSq=-1;
    for(const m of caps){
      const fl=(m>>>17)&15;if(fl&F_EP)continue;
      const from=m&127,to=(m>>7)&127,a=b[from]&7,vt=b[to]&7;
      if(a!==B&&a!==R&&a!==Q)continue;
      const val=vt===K?10000:VAL[vt]-(VAL[a]>>2);
      if(val<=best)continue;
      const dr=Math.sign((to>>4)-(from>>4)),df=Math.sign((to&7)-(from&7)),step=dr*16+df;
      if(from+step===to)continue;
      best=val;bestSq=to-step;
    }
    if(bestSq>=0)add(bestSq);
    const ek=this.kings[this.turn];
    if(ek>=0&&res.length<n){
      const r0=ek>>4,want=this.turn?16:-16;
      add(ek+want);for(const o of KO){if(res.length>=n)break;add(ek+o);}
    }
    if(res.length<n){for(const s of [51,52,67,68,50,53,66,69,35,36,83,84])add(s);}
    if(!res.length){for(let s=0;s<120;s++){if(s&0x88){s+=7;continue;}add(s);if(res.length)break;}}
    return res.slice(0,n);
  }
  genFull(n){
    const us=this.turn;const ms=this.gen(false),out=[];
    for(const m of ms){this.make(m);const ds=this.duckCands(n);this.unmake();for(const d of ds)out.push(m|((d+1)<<21));}
    return out;
  }
  nonKing(c){let n=0;const b=this.b;for(let s=0;s<120;s++){if(s&0x88){s+=7;continue;}const p=b[s];if(p&&p!==DUCK&&(p>>3)===c&&(p&7)!==K)n++;}return n;}
  hasPieces(c){const b=this.b;for(let s=0;s<120;s++){if(s&0x88){s+=7;continue;}const p=b[s];if(p&&p!==DUCK&&(p>>3)===c)return true;}return false;}
  repCount(){let n=0;const h=this.hist,L=h.length-1;for(let i=L;i>=0&&i>=L-this.half;i-=2)if(h[i]===this.h1)n++;return n;}
  isRep(){const h=this.hist,L=h.length-1;for(let i=L-2;i>=0&&i>=L-this.half;i-=2)if(h[i]===this.h1)return true;return false;}
  insufficient(){
    const b=this.b;let minors=0,bs=[];
    for(let s=0;s<128;s++){if(s&0x88)continue;const t=b[s]&7;if(!t||t===K||b[s]===DUCK)continue;if(t===P||t===R||t===Q)return false;minors++;if(t===B)bs.push(((s>>4)+(s&7))&1);}
    if(minors<=1)return true;
    return minors===bs.length&&bs.every(x=>x===bs[0]);
  }
  // game result for the side to move, or null if the game goes on
  result(L){
    const v=this.v,us=this.turn,them=us^1;
    if(!v.anti&&!v.setup){
      if(this.kings[them]<0&&!(v.horde&&them===0))return {winner:us,reason:v.atomic?'King exploded':'King captured'};
      if(this.kings[us]<0&&!(v.horde&&us===0))return {winner:them,reason:v.atomic?'King exploded':'King captured'};
    }
    if(v.koth&&this.kings[them]>=0&&CENTER[this.kings[them]])return {winner:them,reason:'King reached the hill'};
    if(v.three&&this.chk[them]>=3)return {winner:them,reason:'Three checks'};
    if(v.racing){
      const w8=this.kings[0]>=0&&(this.kings[0]>>4)===0,b8=this.kings[1]>=0&&(this.kings[1]>>4)===0;
      if(w8&&b8)return {winner:-1,reason:'Both kings reached the finish'};
      if(b8)return {winner:1,reason:'King reached the finish'};
      if(w8&&us===0)return {winner:0,reason:'King reached the finish'};
      if(w8&&us===1){
        L=L||this.legal();
        if(!L.some(m=>this.racingFinish(m)))return {winner:0,reason:'King reached the finish'};
      }
    }
    if(v.horde&&!this.hasPieces(0))return {winner:1,reason:'All white pieces captured'};
    if(v.anti&&!this.hasPieces(us))return {winner:us,reason:'All pieces lost'};
    L=L||this.legal();
    if(!L.length){
      if(v.anti)return {winner:us,reason:'No moves left'};
      if(v.duck)return {winner:us,reason:'Stalemate'};
      if(this.inCheck(us)||(v.secret&&this.secretThreat(us)))return {winner:them,reason:'Checkmate'};
      if(v.staleWin)return {winner:them,reason:'Stalemate (a win in Shatranj)'};
      return {winner:-1,reason:'Stalemate'};
    }
    if(v.bare){const mu=this.nonKing(us),mt=this.nonKing(them);
      if(!mu&&!mt)return {winner:-1,reason:'Both kings bare'};
      if(!mu&&!(mt===1&&L.some(m=>this.isCap(m))))return {winner:them,reason:'Bare king'};}
    if(v.insuf&&!this.inSetup()&&this.insufficient())return {winner:-1,reason:'Insufficient material'};
    if(!v.no50&&this.half>=100)return {winner:-1,reason:'50-move rule'};
    if(!v.prog&&this.repCount()>=3)return {winner:-1,reason:'Threefold repetition'};
    return null;
  }
  racingFinish(m){if((m>>>17)&15)return false;const f=m&127;return this.b[f]===(K|BL)&&(((m>>7)&127)>>4)===0;}
  san(m,L){
    L=L||this.legal();
    const to=(m>>7)&127,pr=(m>>14)&7,fl=(m>>>17)&15,dk=(m>>>21)&127,base=m&((1<<21)-1);
    const b=this.b;let s;
    if(fl&F_DROP)s=(m&127)===P?'P@'+sqName(to):'.PNBRQK'[m&127]+'@'+sqName(to);
    else if(fl&F_CASTLE)s=(to&7)>((m&127)&7)?'O-O':'O-O-O';
    else{
      const from=m&127,p=b[from],t=p&7,cap=this.isCap(m);
      const pd=this.turn?16:-16,pawnLike=t===P&&(cap?(to===from+pd-1||to===from+pd+1):(to===from+pd||(to===from+2*pd&&(from>>4)===(this.turn?1:6)&&!b[from+pd])));
      if(t===P&&this.v.secret&&from===this.sec[this.turn]&&!pawnLike){s='P'+sqName(from)+(cap?'x':'-')+sqName(to);}
      else if(t===P){s=cap?FILES[from&7]+'x':'';s+=sqName(to);if(pr)s+='='+'.PNBRQK'[pr];}
      else{
        s='.PNBRQK'[t];
        const amb=L.filter(x=>((x>>>17)&15&(F_DROP|F_CASTLE))===0&&(x&127)!==from&&((x>>7)&127)===to&&b[x&127]===p);
        if(amb.length){
          const sf=amb.some(x=>(x&7)===(from&7)),sr=amb.some(x=>((x&127)>>4)===(from>>4));
          if(!sf)s+=FILES[from&7];else if(!sr)s+=(8-(from>>4));else s+=sqName(from);
        }
        if(cap)s+='x';s+=sqName(to);
      }
    }
    this.make(m);
    const r=this.result();
    if(r&&r.winner===(this.turn^1)&&r.reason!=='Stalemate')s+='#';
    else if(this.inCheck(this.turn))s+='+';
    this.unmake();
    if(dk)s+=' 🦆'+sqName(dk-1);
    return s;
  }
  uci(m){
    const to=(m>>7)&127,pr=(m>>14)&7,fl=(m>>>17)&15,dk=(m>>>21)&127;let s;
    if(fl&F_DROP)s=PCH[m&127].toUpperCase()+'@'+sqName(to);
    else if(fl&F_CASTLE&&!this.v.c960){const kf=m&127,base=this.turn?0:112;s=sqName(kf)+sqName(base+((to&7)>(kf&7)?6:2));}
    else s=sqName(m&127)+sqName(to)+(pr?PCH[pr]:'');
    if(dk)s+=','+sqName(dk-1);
    return s;
  }
  fromUci(u,L){
    L=L||this.legal();
    let duck=0;if(u.includes(',')){const parts=u.split(',');u=parts[0];duck=nameSq(parts[1])+1;}
    for(const m of L){
      const base=m&((1<<21)-1);
      if(this.uci(base)===u)return base|(duck<<21);
      if(((m>>>17)&F_CASTLE)&&sqName(m&127)+sqName((m>>7)&127)===u)return base|(duck<<21);
    }
    return 0;
  }
}

/* ---------------- evaluation ---------------- */
const PST=[null,
[0,0,0,0,0,0,0,0,50,50,50,50,50,50,50,50,10,10,20,30,30,20,10,10,5,5,10,25,25,10,5,5,0,0,0,20,20,0,0,0,5,-5,-10,0,0,-10,-5,5,5,10,10,-20,-20,10,10,5,0,0,0,0,0,0,0,0],
[-50,-40,-30,-30,-30,-30,-40,-50,-40,-20,0,0,0,0,-20,-40,-30,0,10,15,15,10,0,-30,-30,5,15,20,20,15,5,-30,-30,0,15,20,20,15,0,-30,-30,5,10,15,15,10,5,-30,-40,-20,0,5,5,0,-20,-40,-50,-40,-30,-30,-30,-30,-40,-50],
[-20,-10,-10,-10,-10,-10,-10,-20,-10,0,0,0,0,0,0,-10,-10,0,5,10,10,5,0,-10,-10,5,5,10,10,5,5,-10,-10,0,10,10,10,10,0,-10,-10,10,10,10,10,10,10,-10,-10,5,0,0,0,0,5,-10,-20,-10,-10,-10,-10,-10,-10,-20],
[0,0,0,0,0,0,0,0,5,10,10,10,10,10,10,5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,0,0,0,5,5,0,0,0],
[-20,-10,-10,-5,-5,-10,-10,-20,-10,0,0,0,0,0,0,-10,-10,0,5,5,5,5,0,-10,-5,0,5,5,5,5,0,-5,0,0,5,5,5,5,0,-5,-10,5,5,5,5,5,0,-10,-10,0,5,0,0,0,0,-10,-20,-10,-10,-5,-5,-10,-10,-20],
[-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-20,-30,-30,-40,-40,-30,-30,-20,-10,-20,-20,-20,-20,-20,-20,-10,20,20,0,0,0,0,20,20,20,30,10,0,0,10,30,20]];
const KEND=[-50,-40,-30,-20,-20,-30,-40,-50,-30,-20,-10,0,0,-10,-20,-30,-30,-10,20,30,30,20,-10,-30,-30,-10,30,40,40,30,-10,-30,-30,-10,30,40,40,30,-10,-30,-30,-10,20,30,30,20,-10,-30,-30,-30,0,0,0,0,-30,-30,-50,-30,-30,-30,-30,-30,-30,-50];
const PEND=[0,90,60,35,20,10,0,0];
const PHASE=[0,0,1,1,2,4,0];
const ANTIV=[0,100,250,250,300,350,200];
function cdist(s){const r=s>>4,f=s&7;return Math.max(3-r,r-4)+Math.max(3-f,f-4);}

function evaluate(pos){
  const b=pos.b,v=pos.v;
  if(v.anti){
    let sc=0;
    for(let s=0;s<120;s++){if(s&0x88){s+=7;continue;}const p=b[s];if(!p)continue;const w=ANTIV[p&7];if(p>>3)sc+=w;else sc-=w;}
    return pos.turn?-sc:sc;
  }
  let mg=0,eg=0,phase=0,bish0=0,bish1=0;
  for(let s=0;s<120;s++){
    if(s&0x88){s+=7;continue;}
    const p=b[s];if(!p||p===DUCK)continue;
    const t=p&7,blk=p>>3,i64=((s>>4)<<3)|(s&7),idx=blk?i64^56:i64;
    phase+=PHASE[t];
    const vt=v.anc?(t===Q?(v.makruk?180:150):t===B?(v.khon?260:110):VAL[t]):VAL[t];
    let m=vt+PST[t][idx],e=vt;
    if(t===K){
      e=KEND[idx];m=PST[6][idx];
      if(v.koth){const d=cdist(s);m=e=(6-d)*35;}
      else if(v.racing){const adv=7-(s>>4);m=e=adv*90+(adv>=6?150:0);}
      else if(v.three){m-=20;}
    }
    else if(t===P){e+=PEND[blk?7-(i64>>3):(i64>>3)]+PST[1][idx]*0.3;if(v.horde&&!blk){m-=0;}}
    else e+=PST[t][idx]*0.6;
    if(t===B){if(blk)bish1++;else bish0++;}
    if(blk){mg-=m;eg-=e;}else{mg+=m;eg+=e;}
  }
  if(bish0>=2){mg+=30;eg+=40;}if(bish1>=2){mg-=30;eg-=40;}
  if(phase>24)phase=24;
  if(v.zh||(v.setup&&pos.inSetup()))phase=24;
  let sc=(mg*phase+eg*(24-phase))/24;
  if(v.zh){for(let t=1;t<=5;t++)sc+=(pos.pock[t]-pos.pock[8+t])*VAL[t]*0.9;}
  if(v.secret)sc+=(pos.sec[0]>=0?1000:0)-(pos.sec[1]>=0?1000:0)+(pos.pend[0]>=0?790:0)-(pos.pend[1]>=0?790:0);
  if(v.setup){for(let t=1;t<=5;t++)sc+=(pos.pock[t]-pos.pock[8+t])*(VAL[t]+20);}
  if(v.three){const bon=[0,140,420,1000];sc+=bon[pos.chk[0]]-bon[pos.chk[1]];}
  if(!v.koth&&!v.racing&&!v.horde&&phase<=8&&pos.kings[0]>=0&&pos.kings[1]>=0&&Math.abs(sc)>250){
    const win=sc>0?0:1,lk=pos.kings[win^1],wk=pos.kings[win];
    const kd=Math.abs((lk>>4)-(wk>>4))+Math.abs((lk&7)-(wk&7));
    const bonus=cdist(lk)*12+(14-kd)*5;
    sc+=win===0?bonus:-bonus;
  }
  sc|=0;
  return pos.turn?-sc:sc;
}

/* ---------------- search ---------------- */
const TTBITS=19,TTSIZE=1<<TTBITS,TTMASK=TTSIZE-1;
const ttKey=new Int32Array(TTSIZE),ttMove=new Int32Array(TTSIZE),ttScore=new Int16Array(TTSIZE),ttDepth=new Int8Array(TTSIZE),ttFlag=new Int8Array(TTSIZE);
const EXACT=1,LOWER=2,UPPER=3;
const now=()=>(typeof performance!=='undefined'?performance.now():Date.now());

function think(pos,o){
  const v=pos.v;
  ttKey.fill(0);
  const S={nodes:0,stop:false,deadline:now()+(o.time||1e9),killers:new Int32Array(256),hist:new Int32Array(17*128),jit:o.jitter?(Math.random()*0x7fffffff)|0:0};
  const ev=S.jit?(p)=>evaluate(p)+(((Math.imul(p.h1^S.jit,0x9E3779B1))>>>28)-8):evaluate;
  const checks=!!v.checks;
  const BASEMASK=(1<<21)-1;

  function moveList(caps){
    if(v.duck)return caps?pos.genFull(1).filter(m=>pos.isCap(m)):pos.genFull(2);
    let ms=pos.gen(caps);
    if(v.anti){const c=ms.filter(m=>pos.isCap(m));if(c.length)ms=c;}
    return ms;
  }
  function scoreMoves(ms,ttm,ply){
    const b=pos.b,sc=new Int32Array(ms.length);
    for(let i=0;i<ms.length;i++){
      const m=ms[i];
      if(m===ttm){sc[i]=1e7;continue;}
      const to=(m>>7)&127,fl=(m>>>17)&15,pr=(m>>14)&7;
      if(fl&F_DROP){sc[i]=S.hist[(m&127)*128+to]+(m&127)*3;continue;}
      const v2=(fl&F_CASTLE)?0:b[to]&7,a=b[m&127]&7;
      if(v2&&b[to]!==DUCK)sc[i]=1e6+VAL[v2]*10-VAL[a]/10+(v2===K?1e5:0);
      else if(fl&F_EP)sc[i]=1e6+1000;
      else if(pr)sc[i]=9e5+pr;
      else if((m&BASEMASK)===S.killers[ply*2])sc[i]=8e5;
      else if((m&BASEMASK)===S.killers[ply*2+1])sc[i]=7e5;
      else sc[i]=S.hist[(b[m&127]&15)*128+to];
    }
    return sc;
  }
  function pick(ms,sc,i){
    let bi=i;for(let j=i+1;j<ms.length;j++)if(sc[j]>sc[bi])bi=j;
    if(bi!==i){let t=ms[i];ms[i]=ms[bi];ms[bi]=t;t=sc[i];sc[i]=sc[bi];sc[bi]=t;}
    return ms[i];
  }
  // returns a score if the position is decided, otherwise null
  function terminal(ply){
    const us=pos.turn,them=us^1,k=pos.kings;
    if(!v.anti&&!v.setup){
      if(k[us]<0&&!(v.horde&&us===0))return -MATE+ply;
      if(k[them]<0&&!(v.horde&&them===0))return MATE-ply;
    }
    if(v.koth&&k[them]>=0&&CENTER[k[them]])return -MATE+ply;
    if(v.three&&pos.chk[them]>=3)return -MATE+ply;
    if(v.racing){
      const w8=k[0]>=0&&(k[0]>>4)===0,b8=k[1]>=0&&(k[1]>>4)===0;
      if(w8&&b8)return 0;
      if(b8)return us===1?MATE-ply:-MATE+ply;
      if(w8){
        if(us===0)return MATE-ply;
        const L=pos.legal();return L.some(m=>pos.racingFinish(m))?0:-MATE+ply;
      }
    }
    if(v.horde&&us===0&&!pos.hasPieces(0))return -MATE+ply;
    if(v.anti&&!pos.hasPieces(us))return MATE-ply;
    if(v.bare){const mu=pos.nonKing(us),mt=pos.nonKing(them);if(!mu&&!mt)return 0;if(!mu&&mt>1)return -MATE+ply;}
    return null;
  }
  function noMoves(ply,inChk){
    if(v.anti||v.duck)return MATE-ply;
    if(inChk||(v.secret&&pos.secretThreat(pos.turn)))return -MATE+ply;
    return v.staleWin?-MATE+ply:0;
  }
  function qs(alpha,beta,ply,qd){
    if((++S.nodes&2047)===0&&now()>S.deadline)S.stop=true;
    if(S.stop)return 0;
    const tr=terminal(ply);if(tr!==null)return tr;
    const us=pos.turn;
    const ms=moveList(true);
    const forced=v.anti&&ms.length>0&&qd<6;
    let stand=-INF;
    if(!forced){
      stand=ev(pos);
      if(stand>=beta||ply>60)return stand;
      if(stand>alpha)alpha=stand;
    }
    const sc=scoreMoves(ms,0,ply);
    let any=false;
    for(let i=0;i<ms.length;i++){
      const m=pick(ms,sc,i);
      if(!forced&&!((m>>14)&7)){const vt=pos.b[(m>>7)&127]&7;if(vt!==K&&!v.atomic&&stand+VAL[vt]+200<alpha)continue;}
      pos.make(m);
      if(!pos.okAfter(us)){pos.unmake();continue;}
      any=true;
      const s=(pos.turn!==us)?-qs(-beta,-alpha,ply+1,qd+1):qs(alpha,beta,ply+1,qd+1);
      pos.unmake();
      if(S.stop)return 0;
      if(s>alpha){if(s>=beta)return s;alpha=s;}
    }
    if(forced&&!any)return ev(pos);
    return alpha;
  }
  function nega(depth,alpha,beta,ply,allowNull){
    if((++S.nodes&2047)===0&&now()>S.deadline)S.stop=true;
    if(S.stop)return 0;
    if(ply>0){
      const tr=terminal(ply);if(tr!==null)return tr;
      if((!v.no50&&pos.half>=100)||(!v.prog&&pos.isRep()))return 0;
    }
    const us=pos.turn,inChk=checks&&pos.inCheck(us);
    if(inChk)depth++;
    if(depth<=0)return qs(alpha,beta,ply,0);
    if(ply>90)return ev(pos);
    const idx=pos.h1&TTMASK;let ttm=0;
    if(ttKey[idx]===pos.h2){
      ttm=ttMove[idx];
      if(ttDepth[idx]>=depth){
        let s=ttScore[idx];if(s>MATE-500)s-=ply;else if(s<-MATE+500)s+=ply;
        const f=ttFlag[idx];
        if(f===EXACT||(f===LOWER&&s>=beta)||(f===UPPER&&s<=alpha))return s;
      }
    }
    if(allowNull&&!v.prog&&!inChk&&depth>=3&&!v.anti&&!v.duck&&!v.racing&&beta<MATE-500&&pos.kings[us]>=0&&hasPieces(us)){
      pos.makeNull();
      const s=-nega(depth-1-(depth>6?3:2),-beta,-beta+1,ply+1,false);
      pos.unmakeNull();
      if(S.stop)return 0;
      if(s>=beta)return beta;
    }
    const ms=moveList(false),sc=scoreMoves(ms,ttm,ply);
    let best=-INF,bestM=0,legal=0;const a0=alpha;
    for(let i=0;i<ms.length;i++){
      const m=pick(ms,sc,i);
      const isCap=pos.isCap(m),pr=(m>>14)&7;
      pos.make(m);
      if(!pos.okAfter(us)){pos.unmake();continue;}
      legal++;
      let s;
      if(v.prog)s=(pos.turn!==us)?-nega(depth-1,-beta,-alpha,ply+1,false):nega(depth-1,alpha,beta,ply+1,false);
      else if(legal===1)s=-nega(depth-1,-beta,-alpha,ply+1,true);
      else{
        let red=0;
        if(depth>=3&&legal>3&&!isCap&&!pr&&!inChk&&!(checks&&pos.inCheck(pos.turn)))red=legal>10?2:1;
        s=-nega(depth-1-red,-alpha-1,-alpha,ply+1,true);
        if(s>alpha&&red)s=-nega(depth-1,-alpha-1,-alpha,ply+1,true);
        if(s>alpha&&s<beta)s=-nega(depth-1,-beta,-alpha,ply+1,true);
      }
      pos.unmake();
      if(S.stop)return 0;
      if(s>best){
        best=s;bestM=m;
        if(s>alpha){
          alpha=s;
          if(s>=beta){
            if(!isCap){const bm=m&BASEMASK;if(S.killers[ply*2]!==bm){S.killers[ply*2+1]=S.killers[ply*2];S.killers[ply*2]=bm;}const fl=(m>>>17)&15;S.hist[((fl&F_DROP)?(m&127):(pos.b[m&127]&15))*128+((m>>7)&127)]+=depth*depth;}
            break;
          }
        }
      }
    }
    if(!legal)return noMoves(ply,inChk);
    let st=best;if(st>MATE-500)st+=ply;else if(st<-MATE+500)st-=ply;
    ttKey[idx]=pos.h2;ttMove[idx]=bestM;ttScore[idx]=st;ttDepth[idx]=depth;ttFlag[idx]=best>=beta?LOWER:best>a0?EXACT:UPPER;
    return best;
  }
  function hasPieces(us){const b=pos.b;for(let s=0;s<120;s++){if(s&0x88){s+=7;continue;}const p=b[s];if(p&&p!==DUCK&&(p>>3)===us){const t=p&7;if(t!==P&&t!==K)return true;}}return false;}

  const rootTurn=pos.turn;
  let root=pos.legal();
  if(o.allowed){const A=new Set(o.allowed);const r2=root.filter(m=>A.has(pos.uci(m)));if(r2.length)root=r2;}
  if(v.duck){const ok=new Set(root);root=pos.genFull(3).filter(m=>ok.has(m&BASEMASK));}
  if(!root.length)return {move:0,score:0,depth:0};
  if(root.length===1)return {move:root[0],score:0,depth:0};
  // take an immediate win when there is one
  for(const m of root){pos.make(m);const r=pos.result();pos.unmake();if(r&&r.winner===pos.turn)return {move:m,score:MATE,depth:1};}

  if(o.mode==='noisy'){
    if(Math.random()<(o.blunder||0))return {move:root[(Math.random()*root.length)|0],score:0,depth:0};
    const scored=[];
    for(const m of root){
      pos.make(m);
      const fl=pos.turn!==rootTurn;
      let s=o.depth<=1?(fl?-qs(-INF,INF,1,0):qs(-INF,INF,1,0)):(fl?-nega(o.depth-1,-INF,INF,1,true):nega(o.depth-1,-INF,INF,1,true));
      pos.unmake();
      scored.push({m,s:s+(Math.random()*2-1)*(o.noise||0)});
    }
    scored.sort((a,b)=>b.s-a.s);
    return {move:scored[0].m,score:scored[0].s|0,depth:o.depth};
  }

  const t0=now();
  let order=root.slice(),bestMove=root[0],bestScore=0,done=0;
  for(let d=1;d<=(o.maxDepth||64);d++){
    let alpha=-INF,beta=INF,curBest=0,curScore=-INF;
    for(let i=0;i<order.length;i++){
      const m=order[i];
      pos.make(m);
      let s;
      if(v.prog)s=(pos.turn!==rootTurn)?-nega(d-1,-beta,-alpha,1,false):nega(d-1,alpha,beta,1,false);
      else if(i===0)s=-nega(d-1,-beta,-alpha,1,true);
      else{s=-nega(d-1,-alpha-1,-alpha,1,true);if(s>alpha&&!S.stop)s=-nega(d-1,-beta,-alpha,1,true);}
      pos.unmake();
      if(S.stop)break;
      if(s>curScore){curScore=s;curBest=m;}
      if(s>alpha)alpha=s;
    }
    if(S.stop)break;
    bestMove=curBest;bestScore=curScore;done=d;
    order.splice(order.indexOf(curBest),1);order.unshift(curBest);
    if(Math.abs(bestScore)>MATE-200)break;
    if(o.time&&now()-t0>o.time*0.55)break;
  }
  return {move:bestMove,score:bestScore,depth:done,nodes:S.nodes};
}

return {Pos,think,evaluate,sqName,nameSq,START,startFen,VARIANTS,P,N,B,R,Q,K,BL,DUCK,F_EP,F_CASTLE,F_DOUBLE,F_DROP};
}
