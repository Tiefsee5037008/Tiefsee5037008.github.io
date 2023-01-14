---
title: IrisCTF writeup for Meaning of Python 2
category: [Writeup, Contests] 
tags: [reverse, python, ctf]
---
# Challenge
[python2.py]({% link /assets/python2.py %})
# Solution
Before start:

with the syntax highlighting, we can see that there is a huge byte literal(begin with `b'`), meaning that this may be the core content of the program.

To see how the control flow goes, let's first deal with the part before that:

Noticing there are many hex-encoded strings(`'\xhh'`), we can use `print()` to reveal them
```py
print("""WWXWXWXXXXXWWWWXXWWXXWX,lIIIlIIIllIllIIllIII,LILJIJJIJJILLIIJJLL,S2S2SS2S222S2S2SS2222,wxwwxxwwwxxxxwxxxwxx=(lambda wxxwwxwxwxxxwwxwwwwxw:wxxwwxwxwxxxwwxwwwwxw(__import__('\x7a\x6c\x69\x62'))),(lambda wxxwwxwxwxxxwwxwwwwxw:wxxwwxwxwxxxwwxwwwwxw['\x64\x65\x63\x6f\x6d\x70\x72\x65\x73\x73']),(lambda wxxwwxwxwxxxwwxwwwwxw:globals()['\x65\x76\x61\x6c'](globals()['\x63\x6f\x6d\x70\x69\x6c\x65'](globals()['\x73\x74\x72']("\x67\x6c\x6f\x62\x61\x6c\x73\x28\x29\x5b\x27\x5c\x78\x36\x35\x5c\x78\x37\x36\x5c\x78\x36\x31\x5c\x78\x36\x63\x27\x5d(wxxwwxwxwxxxwwxwwwwxw)"),filename='\x6e\x6d\x6e\x6e\x6e\x6d\x6e\x6e\x6e\x6e\x6d\x6e\x6e\x6e\x6e\x6e\x6d\x6e\x6e\x6d\x6e\x6e\x6d\x6e\x6e',mode='\x65\x76\x61\x6c'))),(lambda DDDDDDOOooOoDoDooD,wxxwwxwxwxxxwwxwwwwxw:DDDDDDOOooOoDoDooD(wxxwwxwxwxxxwwxwwwwxw)),(lambda:(lambda wxxwwxwxwxxxwwxwwwwxw:globals()['\x65\x76\x61\x6c'](globals()['\x63\x6f\x6d\x70\x69\x6c\x65'](globals()['\x73\x74\x72']("\x67\x6c\x6f\x62\x61\x6c\x73\x28\x29\x5b\x27\x5c\x78\x36\x35\x5c\x78\x37\x36\x5c\x78\x36\x31\x5c\x78\x36\x63\x27\x5d(wxxwwxwxwxxxwwxwwwwxw)"),filename='\x6e\x6d\x6e\x6e\x6e\x6d\x6e\x6e\x6e\x6e\x6d\x6e\x6e\x6e\x6e\x6e\x6d\x6e\x6e\x6d\x6e\x6e\x6d\x6e\x6e',mode='\x65\x76\x61\x6c')))('\x5f\x5f\x69\x6d\x70\x6f\x72\x74\x5f\x5f\x28\x27\x62\x75\x69\x6c\x74\x69\x6e\x73\x27\x29\x2e\x65\x78\x65\x63'));wxwwxxwwwxxxxwxxxwxx()(S2S2SS2S222S2S2SS2222(lIIIlIIIllIllIIllIII(WWXWXWXXXXXWWWWXXWWXXWX(LILJIJJIJJILLIIJJLL('\x76\x61\x72\x73')))""")
```
output:
```
WWXWXWXXXXXWWWWXXWWXXWX,lIIIlIIIllIllIIllIII,LILJIJJIJJILLIIJJLL,S2S2SS2S222S2S2SS2222,wxwwxxwwwxxxxwxxxwxx=(lambda wxxwwxwxwxxxwwxwwwwxw:wxxwwxwxwxxxwwxwwwwxw(__import__('zlib'))),(lambda wxxwwxwxwxxxwwxwwwwxw:wxxwwxwxwxxxwwxwwwwxw['decompress']),(lambda wxxwwxwxwxxxwwxwwwwxw:globals()['eval'](globals()['compile'](globals()['str']("globals()['\x65\x76\x61\x6c'](wxxwwxwxwxxxwwxwwwwxw)"),filename='nmnnnmnnnnmnnnnnmnnmnnmnn',mode='eval'))),(lambda DDDDDDOOooOoDoDooD,wxxwwxwxwxxxwwxwwwwxw:DDDDDDOOooOoDoDooD(wxxwwxwxwxxxwwxwwwwxw)),(lambda:(lambda wxxwwxwxwxxxwwxwwwwxw:globals()['eval'](globals()['compile'](globals()['str']("globals()['\x65\x76\x61\x6c'](wxxwwxwxwxxxwwxwwwwxw)"),filename='nmnnnmnnnnmnnnnnmnnmnnmnn',mode='eval')))('__import__('builtins').exec'));wxwwxxwwwxxxxwxxxwxx()(S2S2SS2S222S2S2SS2222(lIIIlIIIllIllIIllIII(WWXWXWXXXXXWWWWXXWWXXWX(LILJIJJIJJILLIIJJLL('vars')))
```
some part are double-encoded, do it again:
```py
print("""WWXWXWXXXXXWWWWXXWWXXWX,lIIIlIIIllIllIIllIII,LILJIJJIJJILLIIJJLL,S2S2SS2S222S2S2SS2222,wxwwxxwwwxxxxwxxxwxx=(lambda wxxwwxwxwxxxwwxwwwwxw:wxxwwxwxwxxxwwxwwwwxw(__import__('zlib'))),(lambda wxxwwxwxwxxxwwxwwwwxw:wxxwwxwxwxxxwwxwwwwxw['decompress']),(lambda wxxwwxwxwxxxwwxwwwwxw:globals()['eval'](globals()['compile'](globals()['str']("globals()['\x65\x76\x61\x6c'](wxxwwxwxwxxxwwxwwwwxw)"),filename='nmnnnmnnnnmnnnnnmnnmnnmnn',mode='eval'))),(lambda DDDDDDOOooOoDoDooD,wxxwwxwxwxxxwwxwwwwxw:DDDDDDOOooOoDoDooD(wxxwwxwxwxxxwwxwwwwxw)),(lambda:(lambda wxxwwxwxwxxxwwxwwwwxw:globals()['eval'](globals()['compile'](globals()['str']("globals()['\x65\x76\x61\x6c'](wxxwwxwxwxxxwwxwwwwxw)"),filename='nmnnnmnnnnmnnnnnmnnmnnmnn',mode='eval')))('__import__('builtins').exec'));wxwwxxwwwxxxxwxxxwxx()(S2S2SS2S222S2S2SS2222(lIIIlIIIllIllIIllIII(WWXWXWXXXXXWWWWXXWWXXWX(LILJIJJIJJILLIIJJLL('vars')))""")
```
We can almost see something from it:
```
WWXWXWXXXXXWWWWXXWWXXWX,lIIIlIIIllIllIIllIII,LILJIJJIJJILLIIJJLL,S2S2SS2S222S2S2SS2222,wxwwxxwwwxxxxwxxxwxx=(lambda wxxwwxwxwxxxwwxwwwwxw:wxxwwxwxwxxxwwxwwwwxw(__import__('zlib'))),(lambda wxxwwxwxwxxxwwxwwwwxw:wxxwwxwxwxxxwwxwwwwxw['decompress']),(lambda wxxwwxwxwxxxwwxwwwwxw:globals()['eval'](globals()['compile'](globals()['str']("globals()['eval'](wxxwwxwxwxxxwwxwwwwxw)"),filename='nmnnnmnnnnmnnnnnmnnmnnmnn',mode='eval'))),(lambda DDDDDDOOooOoDoDooD,wxxwwxwxwxxxwwxwwwwxw:DDDDDDOOooOoDoDooD(wxxwwxwxwxxxwwxwwwwxw)),(lambda:(lambda wxxwwxwxwxxxwwxwwwwxw:globals()['eval'](globals()['compile'](globals()['str']("globals()['eval'](wxxwwxwxwxxxwwxwwwwxw)"),filename='nmnnnmnnnnmnnnnnmnnmnnmnn',mode='eval')))('__import__('builtins').exec'));wxwwxxwwwxxxxwxxxwxx()(S2S2SS2S222S2S2SS2222(lIIIlIIIllIllIIllIII(WWXWXWXXXXXWWWWXXWWXXWX(LILJIJJIJJILLIIJJLL('vars')))
```
In fact, the keywords are "zlib" and "decompress". So we decompress the code start with b'x\x9c' by zlib and get the output.py:
```py
ocals()['ijjjjjiljlijijllijliill']=globals
ijjjjjiljlijijllijliill()['IlIlIlIlIIlIlIIIIlIIlII'[::+-+-(-(+1))]]=dir
ijjjjjiljlijijllijliill()['IIlIIlllllIIIIIlIllIl'[::+-+-(-(+1))]]=getattr
ijjjjjiljlijijllijliill()['MNNNNMMMNNNNNNNMNN']=locals
MNNNNMMMNNNNNNNMNN()['SSSS22S2S22S222222']=__import__
ijjjjjiljlijijllijliill()['O00OoO00o0oooOO0ooOoOo0']=SSSS22S2S22S222222('builtins').vars
ijjjjjiljlijijllijliill()['llIIlIllIllIlllll']=''.join
......
```
Highly-obfuscated definitions. Seems difficult to start.

Let's go down to see what's below:
```py
from builtins import all,dir,exec,print,int,range,open,exit
exec(S2SS2SS2S2S2SSSSS22S222S2)
import sys
import zlib
def nmnmnnnmmmnmnnnnmmmmmnnnn(s,a,b):
    arr=list(s)
    arr[a]=chr(ord(arr[a])^ ord(arr[b]))
    return LLLIIILJJLLLJIILI.join(arr)
def nmnmnnnmmmnmnnnnmmnmmnnnn(s,a,b):
    arr=list(s)
    tmp=arr[a]
    arr[a]=arr[b]
    arr[b]=tmp
    tmp=globals()[LLIJILIIILJLJIJJIJL]
    globals()[jjliiiijljljiiiljjjililjj]=globals()[OOoODODDooDDDODOoOOD]
    globals()[WXWWXWXXWXWXXXXWXWWXWWXW]=tmp
    return iiiljljjijlljjjllli.join(arr)
def xxxwwxxwwwwwwwxxxw(s,a,b):
    arr=bytearray(s)
    arr[b]^=arr[a]
    locals()[IIIIllIllllIllIllIlI]=globals()[IIJLJLJJLJJILLJLL]
    globals()[xxxwxwxwwxxxwxwxw]=globals()[IIIILLIJILJLJLJLILJJL]
    globals()[IIILJJLIILJLILLILLIJLJJII]=locals()[JILLIJILLIJLJLIJIIIIJ]
    return bytes(arr)
def xxwwwxxwwwwwwwxxxw(s,a,b):
    arr=bytearray(s)
    tmp=arr[a]
    arr[a]=arr[b]
    arr[b]=tmp
    return bytes(arr)
def SS2SS2S22S22SSSSSS22S22S2S(flag):
    locals()[S2SSSSSS2SSSSSS2S222S2SS]=IIIllIIIIIlIIIlIllIll
    while mmmnnnnmmnnnmmnmmmmnmnmn:
        if locals()[wxxxxwxwwxxxxxwxxwxxwwxx]==wwxxwwxwxwwxxwwwxxx:
            locals()[IJLJIJJJILLIJILJI]=xxwwwxxwwwwwwwxxxw(locals()[XWWXXWWXXXWWWWXWXXWWWWXW],lijjljjljijiiillijili,SSS22222SSSS222SS222)
            locals()[nmmnmmnnnmmnmnmnnmnnnnm]=xwwxwxxwwwxwwwwxwx
        elif locals()[wwxwwwxwwxwxxwxxxwxxwx]==NNNNMNMNMMNNNMNMMNN:
            locals()[xwxxxwxxxwwxwwwwxxwxxxwww]=xxwwwxxwwwwwwwxxxw(locals()[WXXXWXXWWWWWWWWXXWXWWWWW],nmnmmnnnnnmnmmmmnnmmmmmn,llillliljiijjlijijjiij)
            locals()[LJLIIIJIJJILLJILILI]=XXXXWXXWXXXXXXXWXWXXWXWW
        elif locals()[lIIIlIlIllIIlIlIIIl]==DODooDDoDOOODooOooDoOo:
            locals()[xxxwxxwxxwxwxwxwxwww]=xxwwwxxwwwwwwwxxxw(locals()[SSSS22SSSS2SSSS2SS2],oDDDDOOOOoODODDODOoOooOOD,O000o0000o0O0OoO0000OO)
            locals()[S22S2SS2S22222SSSS22S2S]=MNMNMMMNMMMNMNNNNMNNMMMNM
        elif locals()[nmnnmnmnmmnmmnmmnnnmnnn]==llllIIIIIlIIlIlIIIlIl:
            locals()[OooOoODoDoOooOODoDoOO]=xxxwwxxwwwwwwwxxxw(locals()[DDoDooooDDDDOOoDooOOOD],llIIIllIllIlIIIlllIlIIIlI,SS222S222SSS22SSSS2)
            locals()[wxxxwxxxxwwxxwxxww]=MNNMMNMMNMMNNNMMNN
        elif locals()[OoDOODDODDoDODoOOOoOOo]==MNNNNNNMMNNMMNMMMNMMMNMM:
            locals()[mnnnmmnnnnnmnmnnnmmnmmn]=xxwwwxxwwwwwwwxxxw(locals()[SS2222S2SSSSSS2S2S2S2S],IIIlllIIlIIIIllIlll,ILLIJIIIILIJLLIIJL)
            locals()[xxwxxxwwwxxxwxxxwwxwwwxwx]=ljljlliljjijlljljjjjji
        elif locals()[OOOODODoOOODOoDDDDOoDooOO]==nmnnnmmmmnmmnnmmmn:
            locals()[LLILLLJILIIJLLJLJJ]=xxwwwxxwwwwwwwxxxw(locals()[mmnmnmnnnmnnnmmmnmnmmn],MNNNNNNMMNMNMNMNMNNNM,DoDDoOOODoDoDODoODODDo)
            locals()[JIIJLLJJLLLJIJLLILJJJ]=LIJILLLIIILILJIJI
        elif locals()[xxxxxwxwwwxwxwxwxwxwxx]==nnmmnmmmmnnmmnmmnmnmm:
            locals()[LIJILLIJLJJLLJLLJLJI]=xxwwwxxwwwwwwwxxxw(locals()[xwwxxwxwxwxwwwxxwx],OooDDODooDOODoDoDDOoooODo,S222S2SSS22S22222S2SS)
            locals()[IlllllIlIlllIllIIIlllII]=ijjiljljillljjljjjjjllj
        elif locals()[IIIlllIIIllIIlIIlI]==mmnnnnmmnnmmnnnnnnnnmmmmn:
            locals()[LILJIJJJIIIILLILLIJJJJJ]=xxxwwxxwwwwwwwxxxw(locals()[mnmmnnnmnnmmnnmnmnm],xwwwxxwxwwxxxwwwxxxwwwwwx,WXWWWWWXWXXWXWWXXWWXX)
            locals()[wwwwwxwwxxxxwxxxw]=OOODOOoDOoOODDDoO
        elif locals()[IllIlllllIIIIIIIlIlIIlI]==nnnnnmmnnnnnmnmnn:
            locals()[oDOOooDDODOOOoOOoOoO]=xxwwwxxwwwwwwwxxxw(locals()[iiiililliljliljjjjj],mnmnnnmmnnnnmmmnmnn,OOOO0oO000O000OoO0)
            locals()[O00OooOOOoO00ooOoooO0oO]=mmnmmmnnnnmmnnnnn
        elif locals()[OoDODOODDoooOOoDoOOO]==oDDDDOoDOoOODODoDDO:
            locals()[DODOODoDoooDOooODDDoDoDOD]=xxxwwxxwwwwwwwxxxw(locals()[Oo000O00o0o0o00OoO00O],IlIlIlIIlIIlIIllllIl,MNNMNNNNNMMNNMMMNMMMNNMM)
            locals()[mmnnnnmnnnmnmnnnnnmmnmmnm]=oDOoOooDOOoDOOOooD
        elif locals()[mmnnnmmnnnnnnmnnnnnmnm]==JJIJIIJJLLIIJJILLJLJILL:
            locals()[XWWWXWWXWWXWXWWWWXWXWWXX]=xxxwwxxwwwwwwwxxxw(locals()[SS22SSSS2S2S222222S2S],NNNNMNNNMMNNNNMNM,S2S22S22S2SS2222S2SSS2SS)
            locals()[wwxxwxxxxwxxwwwwxxwwxxw]=oODoOoDDOoDoODODDOo
        elif locals()[ODOoOODoOOooDDDOOD]==xwwxxxwxxwwwwwwxxwwxxxx:
            locals()[xwxwxxxxwxxxwwxxw]=xxxwwxxwwwwwwwxxxw(locals()[NNMMMMMNMMNMNNNMMNM],SS222S2SSS2S2S2S22S2222S,OOoOOooDDDOOoOoDooo)
            locals()[IlIIllIIllIllIIIlIlIIlllI]=O0O0OO0OoOOOoO000Ooo
        elif locals()[NNNMNNNMNMMMNMMNNMMNMMNM]==IIIlIIIIllllIlIIlIIIlIII:
            locals()[WXWXWWWWXXXWXXXXXXXXW]=xxwwwxxwwwwwwwxxxw(locals()[DDOOoDooODDooDoOoDDDOOODO],lljijljiljjjlililliijljj,JIIIIJILIIILLJJJLL)
            locals()[WXXXXXWWWXXWXXXWXXWXWXW]=ijiljllllljllijlljljjiii
        elif locals()[MNMMNMMMNMNMMMNNNNMMMNMNM]==DOODoODOoDDDooODDODo:
            locals()[OooO0O0oooo0o0O0o0o]=xxxwwxxwwwwwwwxxxw(locals()[mnnnmnmnmmmmnmmmmm],MNNNNMNNMMMMNNNMNMM,MNMNNMMNMMMNNNMNMMMMNM)
            locals()[NMMNMNMNNNMNMMMNMMMMNNMN]=nmmnmnnnnnnmmmnmnmn
        elif locals()[jjjlliliijilliijlillljlj]==oDoOOOoooODoooODOOOOo:
            locals()[mnmmnmnnnmmnmnmnnmmmnmmn]=xxxwwxxwwwwwwwxxxw(locals()[OoODDODoODOOoDOoooOooo],OoODOoODOooOODOoDDoo,iijlllilljlljiljjjjj)
            locals()[mmnmmmmnmnnmnmmmmmmmnmmnm]=S2S22SSSS2SS22222S222
        elif locals()[lIllIlllllIlIlIIIlIIlIl]==IllllIIIIlllIIlllIlIIIIll:
            locals()[llIlIlIlIIlIlllIIIIIl]=xxxwwxxwwwwwwwxxxw(locals()[JJJJLJLILJLIIIILJII],SSS2SSS2SSSSS222SS22S2,oDODoOoDoDOoDDooOOODoooD)
            locals()[WWXWWWXWXWWXXXWWXWXWWXX]=SS22SS2S2222222S2S22S
        elif locals()[WWWWWWXWXWXWWXWXWX]==liljljliliiiiiiljijllijil:
            locals()[IJIJIJJJLLILIIIJILIJILL]=xxxwwxxwwwwwwwxxxw(locals()[JIJJLIJLJLLJILJLJ],llIlIIllllIlIlIlIlIIlI,ijljjjjlljijlillllljilj)
            locals()[Oo00OOooO0OOo00Ooo]=O00oOOoOO00OOOooOo00000OOO
        elif locals()[ljlijiilliillljliiljj]==ljiijjllljijliililiij:
            locals()[ODDoooOOooDODOoODDoO]=xxwwwxxwwwwwwwxxxw(locals()[XWWWXWWXWWWWWXWWW],LJLLILJLLJIIIIJLLIL,MNMNMNMNNNNNMMNMMMM)
            locals()[WXWXXXXXWWWWWWWXXXXXX]=jiiillillijlljljjijj
        elif locals()[wwwwxxxxxxwxwwxxwwxwxw]==xxxxxwwwwwwxwxwxwxxwxww:
            locals()[lljilijjjjlljliliji]=xxxwwxxwwwwwwwxxxw(locals()[O0oOOo0o0OOO000O00OOOOOoOO],LIJIIIJJIILLLJILLIIILJIJ,NMMNMMMMNMMMMMNMMNNM)
            locals()[iiijjlilljliillijl]=xxwwxxxwwwwwxxxxwxxxxxxwx
        elif locals()[Oo0OO00o0OO00o000oo]==JLIJLIIJLIJJJLLLJLLLJ:
            locals()[NNNNNMMMMNMMNMNNNNMNN]=xxxwwxxwwwwwwwxxxw(locals()[ooDoODDDDoDDoDoDDDO],SSSSS2S2S2SS22S2SSS2SS,jjilillliiijllijiljl)
            locals()[WWWXWWWWWWWXWWWWWX]=mnmmnmnnnnmnnnmmmnn
        elif locals()[XXWXWWWXWXWXWWXXWWWWWXWW]==WXWXWXWXXWXWXWWXXXWXXW:
            locals()[mmmnnnmnmnmmnmmnmnmmmnn]=xxwwwxxwwwwwwwxxxw(locals()[jlililiiiijlijillliji],SSS2SS222222SS2SSS2S222S22,ljijjiliilljjjliijliijl)
            locals()[llllIIIlIIIllIlII]=OO00O0oO0OOO0o00o0
        elif locals()[ililljliijjjliljllij]==liijiilillijllliiillljill:
            locals()[NMNNNMMMNNMMNNNNMMMMNMNMM]=xxxwwxxwwwwwwwxxxw(locals()[S2222S22SS22S2SSSS2],jjjiljjjijljjjllijiljiiil,S2S2SSS2SS22S2222SSS2S2S2)
            locals()[Ooo000oOoo0O0OOO00OOoOoo]=NNNNNMMMMNMNMMMNMNMNMM
        elif locals()[OooooO00O00Oo00O00oO0OO0Oo]==nmnmmnmmmnmmmnmmm:
            locals()[IlIIIIIlIIIIIlIIIllIIIl]=xxxwwxxwwwwwwwxxxw(locals()[JLLJILLLJLJIILLLJJILIJIL],xxxwxwwxwxxwxwxwww,LJLLILILJLIILJJJL)
            locals()[nmmmmnmmmnmnnnnmmmnnn]=mmnmmmmnmnmnmmnnmmmnm
        elif locals()[XXXXWWWWXWWWXWXWXXWWXX]==jjillliililjilliljli:
            locals()[JILLJJILJLJJLIILIIILJLIJ]=xxxwwxxwwwwwwwxxxw(locals()[IIIIllIIlllIIllIl],IJJILIIJIJLLILIILJ,SS2S2S222S22SS2SS2S22)
            locals()[nnmnmmnmmmmmmnmnmnnmnn]=ljjlllijiijiijjiijlijjjii
        elif locals()[lIIIIIllllIlllIlIIlI]==jillijljilllililjl:
            locals()[IJLJJJLJIJIJJJJILJJIJI]=xxxwwxxwwwwwwwxxxw(locals()[OOoooOOOoO0Oo0OoOO0o],IIlIlIIlIlIIlIIIIlII,liililjiiiijjilijijiliii)
            locals()[lIIIIllIIlIllllII]=nnmmnnnmmmmnmmnmm
        elif locals()[xxxwxxxxwxxxxwwwxwx]==Oo00Ooo0OOo0oOOoOo:
            locals()[IIlIlllIllllllIIIIl]=xxxwwxxwwwwwwwxxxw(locals()[jllljlllljljiiiij],XWWWXXXWWXXWXWXXWXWXXXWWW,S2S2SSS22S2SS22SSSS2222S)
            locals()[MMNMMMNMNNNMMMMMMMMN]=oDoDoOoDOODOOOoODODoO
        elif locals()[NNNMNMNNMMNMNNNMMNMNNMNNM]==DDooDoDDDDOooOooDD:
            locals()[O0O0OOo000o00OOO00O]=xxxwwxxwwwwwwwxxxw(locals()[mnnmnmmmmnnmnnnmmnmmmmmn],xxxxxxwxwxwwxwxwww,SSS22SS22S2S222S2222222S)
            locals()[OOo00OOoOO0o0oO00O0oo]=IlllIIlIllIlIlllII
        elif locals()[OO0OoooOO0OO0o0OoOO0oo]==IIIJJIJLLJILLJIILILILLLJJ:
            locals()[xwwwxwxxxwxwxwxxw]=xxwwwxxwwwwwwwxxxw(locals()[lIIIIIIlllIlIIlIlIIlIIII],NNMNMNMNNMNNNMMMNNNNNNM,XWXXWWWXWWWWWWXXWXXXWWXW)
            locals()[Oo0ooOoOOo0O000oOoOoOOOo]=IJJLILLJJLJLILJIIILIJILL
        elif locals()[nnnmmnmnnnmmnmnmmmnmnmnn]==oDDDooODDODoOoooDOOoDOOD:
            locals()[liilljjjjljijijlllillil]=xxxwwxxwwwwwwwxxxw(locals()[liilljljllllililil],MNNMMNMMMNMMMMNMMM,WXWXWWXXWWWXXWXXXWWXWXX)
            locals()[XWWXWWXXWWXXWWWWXXWXWXXXX]=O00Oo00OOoo0oooOO0oOOOO0
        elif locals()[lijlijljiijilliiijliijl]==xwxwxwxwwwxwwwwwwwwxxxww:
            locals()[nmmnnmmmmnmmnnnmnmnmn]=xxwwwxxwwwwwwwxxxw(locals()[OoOo00O0oOooOOOOo000oo],IIIlllIIIIllIIIlIlI,nnnmmmmnnnmmnnmmmmnnmmm)
            locals()[IlIllIlIllIIIlIIIIlll]=MNNNMNNMMMMNMMMNNMNNMNM
        elif locals()[WWWXXXWWWXWWWWXXWW]==S222SSS2S22SS22SSS222:
            locals()[XWWXXXWXXWWWWXXWXWWX]=xxxwwxxwwwwwwwxxxw(locals()[WWWWXXXWXWWXWXXXXWWW],OO0OOoooo00O0oOoOoOooo0ooo,O00o0OoOoo0o0000ooo)
            locals()[SSSSS222S22SSSSSSS22SS2S22]=XWXWXWXWWWXWWWXXXWWWWXXX
        elif locals()[Oo000OoOO0OoOO0O00ooOoO]==lIIIIIlIllllIllIII:
            locals()[S2222S22SS22222S22S222S2S]=xxxwwxxwwwwwwwxxxw(locals()[jlijiljjljliiliijlij],IIIlIIlIllIIIlIIIlIIl,nnnnmnmmmmmmnnnmmnn)
            locals()[jliillljllljljjiillliljil]=llllIllIlIlIlllIllI
        elif locals()[OODDDDoDDODoODODODODDoO]==DDoOoDDOoDDoOOODoooo:
            locals()[mnnnmmnmmmnmmnmnm]=xxwwwxxwwwwwwwxxxw(locals()[oODOoOOODDDoDoOoOooo],LLIJLJJJJLILILJJIIJIJLJ,NMNMNMMMNMMMMMNMNMMNM)
            locals()[IJILIJIJLIIIIIJII]=NMNNNNMMNMNMNMMMMNMNMMN
        elif locals()[jiillillijjjjilljlljlijij]==S2SSS22222S2222S222:
            locals()[O0Oooo00o0O00o0OO0]=xxxwwxxwwwwwwwxxxw(locals()[mnmmnmmnmmnnmmmnnmmmmn],O0oOoooO0ooo0O0Oo0Oo0000OO,xxwxxxwwwwxxxxxxwwwxxx)
            locals()[OO0OOo0ooooOOo0000oO0OoO0]=ILILJJIIIIIJJJILJJI
        elif locals()[OOoOoO00o0OooOoOO0O]==IIllIllIIIIIIIlIlIIlllI:
            locals()[S2SSSSS2S22SS2SS2S2S]=xxxwwxxwwwwwwwxxxw(locals()[IllIlllIIIIIlllllIlIIlll],nmnmmmmnnmmmnmnmnmnn,mnmnmnmnnmnnmmnmmm)
            locals()[iljlilliljjljjljliji]=MNMNMNNMNMNMNNMMNNM
        elif locals()[MMMNNMNNNNMNNMMMNNNMMN]==jliljjlillijjjjlj:
            locals()[iilijljiliiljljijil]=xxxwwxxwwwwwwwxxxw(locals()[mmnmnnnnmnmmnmnnnmnmmn],mmnmmnnnmnnnnnmmnmmnnmm,OODooOOOoooDoOoDDOODOoD)
            locals()[WXXXWWWWXXXXWWXXXWXX]=SSSS22SS2SSSSS2S22S2S22S2
        elif locals()[xwwwxxxwxxwwwwwwwwxwwx]==JIJJJJLJLIJJIJLIILLJ:
            locals()[mmnmnmmnnnnmmmnnm]=xxwwwxxwwwwwwwxxxw(locals()[S2S2SSS222222SS2SSSSS2],XWWXWWXWWWXWXWXWXXXXWWXXW,OO0o0oo00Oo0o00OOOOo)
            locals()[xwxxxwxwwxxxwxxxwxwxx]=ILLLJJLJJLJLILLLIIIJJ
        elif locals()[WXXXWXXXWWXXWWWWXXXW]==OoO000OOoo0O000OO0:
            locals()[IJLLLJLJIIILIJILLJLJIIIJJ]=xxwwwxxwwwwwwwxxxw(locals()[S2S22SS2S22SS2SS22SSSS],MNMMMMNMMMMMMMMMMNMNMMM,MNMNNNMNMNNMNNMNMM)
            locals()[SS2222SSS2S2SS222S2SSS]=OOoO00OooO0oo0OoO0O
        elif locals()[WWXXWWWWWWXXXWWXXWXXWX]==ljjijijliijljllll:
            locals()[ILJLIJJJJJIJIJIJIIJLLIJ]=xxxwwxxwwwwwwwxxxw(locals()[S2SSS22SSSS2S2S2S222222],DDDDDoOooOOoOoOoOoDDDoO,NMMNNMNMMMMMMMMNNMMMNMN)
            locals()[IIILIJLLIILJIIJJIL]=oODDODODDoDDDoODoOD
        elif locals()[xxxwwwwwwxwwwxxxwxww]==O00O0oO0O00O0o0O00OOo:
            locals()[lIllllIlllllIlIIIlIIIlll]=xxxwwxxwwwwwwwxxxw(locals()[xwwwxwxxwxwxxwwxwwxxw],SS2SSSS2S2SS2S22SS,MNMNMMMNNMNNMMNMNMM)
            locals()[MNMMMNNMMNNNMNMNNMNNMNNNM]=ODOOOoDoDDDOOoDODOO
        elif locals()[IILLJJLLIILJLIIJIILLI]==NMMMMNNNNNMNMNMNMN:
            locals()[LJLIJJJJJLLJLLLJIJIJ]=xxwwwxxwwwwwwwxxxw(locals()[SS2S2S2S2SS2222S22],OoOoo0O0o0O0OooO00o0o,ILJLIJJJJIJJILLLLJ)
            locals()[IllIIIIlIIlIlIlIIIllI]=NNMNMMNNNNMMNNNNNMMNMMMMM
        elif locals()[DoOOOOooooODDoDOODoDDOo]==lIlIlllIIIlIIlIIIlII:
            locals()[LJJLLJIJJJIIIIJLL]=xxwwwxxwwwwwwwxxxw(locals()[OOoOO00O0O0o0Ooo00O],S2SS2222SS2SSS22S2S2S,WXWWWWWXXWWWWWXXXWX)
            locals()[OoOOoo00OOOOoo0O0O00O]=IlIlllIIllllIIIlIll
        elif locals()[Oo00OO0o0oOoooOo0O]==lIlllIlIlIIIllIIll:
            locals()[jiijjjjillillliillllljil]=xxwwwxxwwwwwwwxxxw(locals()[lllIlIIIlIIIlIIlllIIl],MNNNNMNMNNMNMMNMNNMMMNM,S22S2S22S2SS2222S2S2S)
            locals()[lIlllIlIllIIIlIIIIIIIlI]=jiijlijilijijiljijjjilji
        elif locals()[LLLJIJLLLJLIJJIJIJIIJ]==Ooo0oO0000OOo00OOoO00o0o0:
            locals()[MNNMNNMNNNNMMMNNMNMNMNMNN]=xxxwwxxwwwwwwwxxxw(locals()[nmmmnmnnnnnmmnnmnn],O0o0oooOOooOO0o0OO,OoooooooO0Oo00o0O0oooO)
            locals()[OO0O00o00OoOO00o000]=O0OOO0OOoOO000Ooo0
        elif locals()[lIlllIllIIIllllIlllIlI]==XXWWWWXXWXXWWWXWWWW:
            locals()[OoDDDoOOoOooDDoDDDoDDOO]=xxxwwxxwwwwwwwxxxw(locals()[OOoOo0Oooo0oO0000OoO],WWXWWXWWWXXXXWXXWXWXWW,jiiljijliljiijllijili)
            locals()[wxxwwxxwwxwwwwxwwwwwxwxxx]=MNNNNMMNMMMMMMMMNMMMMMNN
        elif locals()[LJJJLJJJJIIIJILJJIJ]==oDoDOoooDOOOODDOooD:
            locals()[xxxxwxwxxxxwwwwwwwxxx]=xxxwwxxwwwwwwwxxxw(locals()[OoOoDoOOOoooODOoODOoooooD],llIIlIIlIIIlIlIlIIlI,LIJLJLJJJJLJIJIJIJLI)
            locals()[SS22SSSS2222222SSS]=iijilijjjjlijliljjj
        elif locals()[IIlIIIllIlllllllIlIllllI]==xxxxxwwxxwxwwwwwx:
            locals()[WWWXXWXXXXXXXXWWWXXXWWX]=xxxwwxxwwwwwwwxxxw(locals()[SS22SSSS2S2SSS222S],WXXXWXXWXXXWXXXWXWW,mnnnmmmnmnmnmnmmnnm)
            locals()[DDDDooDoooDOoODooODoDooO]=O0o0O00oOooooOOO0o
        elif locals()[jijljjiiijjjjljjijljjiij]==WXXWXXXWWXXXWXWXW:
            locals()[OooOoOO0OoOO000OO0ooOo0o]=xxwwwxxwwwwwwwxxxw(locals()[mmmnnnnnmnnnnmmmmmnnn],OoooDoOoODooODOooODO,wxwxwxxwwwxwxxxwxxxwx)
            locals()[OO0oooo0oOOo0OOooo0o0ooOo0]=xxxxxxwxwxwwwxwwwxxx
        elif locals()[S2SSSSSS22S22S22SS2222S]==JIJLLJIIJLLLIJLJJILLILJ:
            locals()[LIJLJLLILIJJIJJJLLIJJLJLL]=xxwwwxxwwwwwwwxxxw(locals()[NMMNMNMMNNMNNMMNNNNMMNN],MNNMNMNMNMNMMMMNMNMMN,LLLJJLIILJIJLILIJLLIIJJL)
            locals()[WXXWWXWWWXXXXWWWWXXWXWX]=JIJLIJJILJLJJJIJIJI
        elif locals()[JILJJLIIILIJLJJJIJLLJ]==llIIllIIlIlIlIlIllIlII:
            locals()[MNNMMMMNNMNNNMMMMNMMM]=xxwwwxxwwwwwwwxxxw(locals()[XWWXWXXXWWWXWWXWW],LIIJLJLILLIJIIILJJILLJ,IlllllIIllIlIIIlIlII)
            locals()[SSS2S2SS2S222SSS2222SS]=WWWXXWWWXWWWXWWWXWWXXX
        elif locals()[WXXXWXWWWXWXXXXWWWXW]==ijlljiiijjjliijli:
            return
def SS2SS2S22S22SSSSSS2SS22S2S(flag):
    locals()[mmmnmnmmmnmmmmmmmmnnm]=xwxwxxxwwxwwwxxxxwxxxx
    while MNNMMNNMNMMMNNMMN:
        if locals()[mnmmnnmmmmnmmmmmnmnnm]==wwxxxwwxxxxwxxwwxxx:
            locals()[IIILILIIJJIILIIJJL]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[Oo00oo0Oo0O00o0o00OoOOo],xwwwxwwwxwxxxxxwwwwwwxxxx,JIJJJJJLIIIJILJIJLLII)
            locals()[WWWXXWWWXWWWXXXWWWXXXW]=ijjjjlilijjiijlij
        elif locals()[MNMMMNNNNNMMMMNNMNNMM]==OODoOODDooDDDOOOODDOOD:
            locals()[OOoOoOo00oooOO0ooOo0o]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[OOooOOo0oO0oo0Oo000o0o0],WXWXXXWWWXWWWXXWWXXW,IllIllllllIllIIIIIlI)
            locals()[S2S22S22SSSSSS2SS2SS]=lIlllllIIllIIlIlllIl
        elif locals()[SSS2SSS2SSSS2SS22S222SS2S]==WWWWWXXWXXWWWXWWX:
            locals()[WWWXWWXWWXXXXXWXW]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[O0oOOOoO00OOo000oOOoOO0O0],Ooo00oOoooo0OOOoooo0oo,llIIIIlllIIlIIllII)
            locals()[LLLJIJJJLIJJLLJILJJJI]=SS2S22S2S22SSSSS22SSSS2S
        elif locals()[SSS2SSSSSS2222SS22S]==MMMMMMNNNMMNNMMNNNN:
            locals()[jlljjjijilljjlillllill]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[mnnmmmnnnmmmmnmnmnmnn],iiilililjiljljjlijii,lIIlIIIlIIlllIIlIIIIIllll)
            locals()[ILLLJLILJLLLJJIILIJLILI]=XWWXWXXWWXWXWWXWXWXWWW
        elif locals()[LLILJLLIJJJJLJJIIIIIJJL]==nmmnmmmmnnnmnnnmnmmn:
            locals()[nmnnnmmnmmnmnmnmmnmn]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[nnnmnmmnnnmnnmnnmnm],Oo0OOoOOOooOOOOO0O0OOo,S2222SSSSS2222S2SSS2)
            locals()[mmmmnmnmnmnnmmmmmnn]=lIIIIlIIIIIllllllIIIIl
        elif locals()[wwwxwwxwwwxxwxwwxwwwwwwwx]==wxxxxwxxwwxxwxxxxwx:
            locals()[ljliiljjjlijljjiijilliji]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[IIILJLLLIIIJJJILLJLJJLII],jijljijililjiijilji,NMNMMMMNMNMMNMMMMNMNNMM)
            locals()[JLILJJJLJILJILJJJJJJILJ]=jjjilliljijiijjjjjlj
        elif locals()[SS222S222SSS2222SS2SSS2S]==OooO0O0O0o00oOooo0:
            locals()[SS22SS222SS2SSS222S2S2S]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[mmmnnnnnmnmnmnnmnnm],ililjiiiljijjljjliil,XWXWWXXXXXXWXXWXWXWXXXXXW)
            locals()[MNMNNMMNNNMMNNNMMNM]=XWWXWXXXWXWWXWWWXX
        elif locals()[wxxwwwxxxwwxxxxwxxwwxwx]==WXXXXWWWWXWXWXXXWXWWWWXW:
            locals()[wwwxxxwxxxxxwwxxxwxwxw]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[NMNMNMMNNNNNNMMMM],wwxwwwwwxxwxxwxwxwwwxw,wwwwxxwxwwxxwwxwxx)
            locals()[OoO0OOo0O0o00o0OOooo0ooOO0]=SSSSS2SSS2S22SS22SS2SSS
        elif locals()[wxwxwxwwwxxwxxwwwxxxx]==OOoOooOOooOoOOoO0000ooO:
            locals()[SS2S2SSSSS2222SSSSS2S2]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[IJJIJIILJJILLLIJJJIIIJJLI],NMMMMNNNNNMMNMNNMNNMNMNMM,MMMMNNMNMMNNMNMMMNMMNNNNM)
            locals()[OooOOOooODDDoDOOO]=llIlIIlIIIlllIIIIlllIlll
        elif locals()[JIJIILJLJJJILLLLJLIIJ]==O00o0OooooOoOO0Oo00OOO0:
            locals()[llIlIIIllIIllllIIlIIIIII]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[lIIllIIIIIllIllIllIlI],OODoDODOoODDDDOOOoD,OoOoooOoo00Oo0O00o0o0o0O0O)
            locals()[NNNMNMMMMNNNNNNMMNNNMNMNM]=WXWWXWWWXXXWXXWWWX
        elif locals()[OO0O0OO00Oooo0oO0O0O0ooo]==WXXWXXXXXWXWWXXXXWWXX:
            locals()[O00O0OOo000OOOoo0O0]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[LLJLLIIIIJILLILJIJ],OoOooOoOoo0OoOO0O0ooO00O,nmmnnmmmmnmmmnmmn)
            locals()[MNMNNNMMNMNNMNNMMN]=xxwxwwwwwwxwxwwwwwwwwxxx
        elif locals()[MNMMNNNMNMNMMMNMNNMN]==IIIIlIllIlIIlIllll:
            locals()[SSSS2S22SS2S2S2SSSS2S]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[OO0OoOo0Ooo0OOooOo0OOO],llIllIlIIllIlIIIlIIlIIll,llIllIlIlIlIlIlIII)
            locals()[O0OOo0OoOOooOoOOOOoO0O00]=MMMMMNNNMMNMMMMMNM
        elif locals()[ILIILJJJILIJLJIILJIIJLJ]==S22S2S2S222S2SS2SS:
            locals()[XWXXWWWWWXXXWXWXX]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[nnnnnnnnnnnmmmmmn],illljjljliiljjlij,NMNNMMNMNMNNMMNNNNMNNNM)
            locals()[NMMNMNNNNMNNNNNNN]=NNMMMNMMNNMNMMMNMNNMNMMM
        elif locals()[NMNNNMMMMMMMNMNMMNMMM]==ODDOOOOODoODDDOoo:
            locals()[Oo0O000oOoooo000oOo0OOo]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[S22S2SSS22S2SS2SS2S2],IllIIlIlIIlIIIlIlIl,MMNMNNMMMMMMMMNNNNMMMNNNM)
            locals()[nmmmnnmnnnmnnmnnmnnmnn]=S2S22S22SS22SSS22SSS2S22S
        elif locals()[JLLJILIJJJIJILIIJL]==SSSSS2SS2222S2S2SS:
            locals()[WXWXXWWXWXXWXWXXXW]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[nmnmnmnmnnmmmnmnm],WXWWXWWWWWWXXWXWWXWXXW,S2S2S22SSS2SS2S2SS2S22S2S)
            locals()[liijjljjjljlllljlljiljj]=xxxwwwxwxxwxxwxwxx
        elif locals()[S22222S222SS2SSS2SS22S2S2]==OooOoODDDOODDOOOoOOD:
            locals()[nmmmnnmnmmnmnnnmnnn]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[DDDoODDDoDOOooDDDDoooDO],NMNNMNNNNNNMMMMNNNMNM,DOOoDOOoDoDOoOoDODOo)
            locals()[XWXWWWXWXWWWXWWWWXX]=lIIlIlIIIllIlIIllIlIlIlII
        elif locals()[JLJJJJILIJLJIJIIJIIJL]==MNMNMNMMMNMNNMNNMMNMMNNN:
            locals()[WWXXXWWWWWXWWXWWXWXWXXX]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[NNMNMMNNMMMMNNMMNMMMNMMMN],JJIJJLLLJIIJLLIIJLJLJIIJL,xwwxxxxwxxxwxwxxxx)
            locals()[oDDODDOooDDDDODDOOoD]=S2SSSS22SS2SS22S2S222
        elif locals()[DDDDDDoODOoDDoODOooO]==S2SS22SSS2SSS2222S2S2S2S2:
            locals()[WWWWXXWWWXXXXWXWXWXWX]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[OO0OoOoOo00ooOOOO00],IllllIIIlllIlIllIllIlII,NMMMMNMNNNMMNNMNNN)
            locals()[jiljjjljjillljlil]=xxwxxwxxxxwxxwxxxwwwxxw
        elif locals()[WXXXWWXXWWXWWXWWWWXWXXXXW]==jjjliiliilijiillllliijljl:
            locals()[XXWXWWXXXXWXXXXWW]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[NMNMNNMMMMNMNNNMMNNMMM],WWWWWXXWWXXXWXXXWWWWX,S222222S2SSSSSS2SS)
            locals()[oDDoooDOooOooOoDDD]=ljiljjiiiijjilillljjill
        elif locals()[MMMMMNNNMNNMMNNNMMNMNMMNM]==iilillillliliiijliji:
            locals()[ILIJIILILLJJJIJIJLLIJII]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[IIIlllIIIIllIIllIIl],oDDDooOOooDDOoDoDOOoDoDo,NMMMNNNNNMNMMNMNMMMNN)
            locals()[mmmnnnmmmnmnnnnnnnmmmn]=liiiljiijjliiillijijjijll
        elif locals()[ljljlijllijljjjiljlllill]==LIJLJLJLJILIILJIJILILI:
            locals()[lllilljilijjijjjijijil]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[ijjjiljljjljjljjiljj],nmnmmmnmnnmnmmmmnmnnm,lilijjlilliijlijiliji)
            locals()[WXXXXWXXWWWXWWXWWXX]=wxwxwxwwxxwxxxxxwwwwxwx
        elif locals()[nmmnnnmmnmnmnmnnnnmmmmmnn]==mnnnnnnmmmmmmmnmnmmm:
            locals()[lIlIlllllIIIIlIIllIllIIll]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[nnnmnnmnnnmnmnnmn],WXWWXXXXWWWWWWXWXXWW,ljjlijlliliiijjiii)
            locals()[ljlililllijjjlljil]=lljjjlijjijlljiiijliij
        elif locals()[llilliijijjlijjllji]==oDOOooOOODOoDOOoOoOoDODOO:
            locals()[XXWXXWXWWXWWXXXXXXXXXXWX]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[jiljiliiijjiiljjiljjjlill],IJIJIIJJJJJIILIJJJLLLJJ,XXXXXXXXXXWWXXWWWWXXWWX)
            locals()[XWXWXWWWXXWWXXWWXWWXW]=lIIlllIIIllIlIIIIIlIlll
        elif locals()[WXWXWXWXXXXXXXXWWXXXXWW]==DoDODDOODOoODODoOOOoOooDO:
            locals()[mnnnnnmmnnmnmnmmmmmmmm]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[MNMNNMMNNMNNMMNNNNN],OooDoODODDDOOODDOODD,JIIIJJJILJIJJJIJJIIL)
            locals()[WWWWWXXWWXXXWWXWXXWXWWX]=xwxwxxwxwxwxxxxwwwwwx
        elif locals()[jjjlliiilllijliijllj]==iljjiliijijijjjiij:
            locals()[ijjjjiiijiijlljlijjlil]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[IIIIIllIIlIllllIl],SS2SS2SS2222SS2S2S2S2SS22,xwwxwxwwxwxwxxxwx)
            locals()[OOoODoooDOOoooDDoDoOoO]=WXXWWXXXWWWXXWWWWXXWWWW
        elif locals()[iiilijijlljjjillijjl]==O0OOoO00oO00o000Oooo0oooo:
            locals()[ILILJLJLLIJJJLIJIILJJL]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[IllllllllllIlIIIIIlII],ODoooOoOOOoDoDDoooDOOOD,SS2SSSSSSSS2S2SSS22SSSS)
            locals()[MNNMNNNNNMMMNNNNN]=wxxwxxxxwwwwxxwxxwxxwx
        elif locals()[nnnmnmnnnnnnnmmmn]==DoDDDoODOoOoODDoDDO:
            locals()[WWXXXXWWWWWXWWXWWWWXWXX]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[OOo0oooO0O00OOooo00ooooO],SSS2SS2SS2SSS2SS2S2,IlIIlIlllIIlllIIIIIIIlI)
            locals()[LLIJJJLLLIJLLJLJIIJJJLLJL]=NNMNNNMNMNNNMMMMNNNMNNNNN
        elif locals()[SSSSS2S22S2SS222SSS2SSS]==ooDDoODODDDDDDOOOO:
            locals()[nmmnnmmnnnmmmnnnmmmm]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[nnnnmnnnmnnmnnmnmmnmmm],DODDOoooDOoODoOOOO,jljljiljiijijllijjijlllij)
            locals()[ooOOODoDoDDDoOOoDOODo]=IlIIIlIIllIIlIIIlIl
        elif locals()[SS22SSS2SSSSSS2SS22S2SSS2]==LILIIJJJJILILIILJJIJJJI:
            locals()[ODDoODooDOoOODOooOOoODOO]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[xwwwxwwxwwwwwwxxwxwxw],DOoDODODDOoOOoOoOoDOoOO,DDDOoOoDOoDOoODOoOODD)
            locals()[xxxwxwwwxwwxxwxxx]=xwxxwwwwwwwxxwwwwxwxw
        elif locals()[JIILJIJLJJJIJJIIJJILJIJII]==XWWXWWXXWWXXWWWXWXXWXXXW:
            locals()[JLIIJLLLJIJLLLJLJI]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[llljjliiilliljjjjjiijjljl],O0oOO0OoO0oo0oooO0O00ooo,O0oO0OOOOOOooo00oOOOOO0)
            locals()[LIJIIILILJLJLJLJLI]=WXWWWWWXWXWWXWXWXXXXXWXXW
        elif locals()[OOOOo0ooooOooo0OO0O]==MMMNMNMNMNMMNMMMM:
            locals()[xxwwwxxxxwxwwxxwxx]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[llIlllIlIlIIIIlIllIIllIIl],DoODODDDOOOOoOoOOOo,DOooDODoODDDOODoOoooOoOoo)
            locals()[OOo0O00o0oo0Oo0O0OOO0]=IllllIIllIlIllIIlIIIIllll
        elif locals()[mnmmnnnnnnmnmnnnmmmmmmnn]==JLJLIJJJIJLIJIJLJIILLL:
            locals()[xwxxwwwxwxwxxwxwwxxxxxxx]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[DoDoDOooOODoOoOoOO],mnmmnnmmnnnnnmnnmmnmnmnm,DDDOODoDDoODooooo)
            locals()[nnnmnnmmnmmnmnnnmnn]=IILJJILLIILLIJIIILILII
        elif locals()[IlllIllIllIIllIlIll]==jljjljilliljiljli:
            locals()[NNMNNNMMMNNNMMMMM]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[JLILLLIIJIIILJLJIJJ],OO000OO00O0o0Oo0o0OO,XXWWXWXXXWXWXXXWXWXX)
            locals()[SS22222S22S222S2SSS22222S]=jijiijjjjljllijilljjllll
        elif locals()[xxwwxxxwxwxxxwxwxwwxw]==ljiilllijjljijijilljjiijl:
            locals()[wwwwwxxwwwwxxxxwwxxxwxww]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[MMNNNNNMNNMNMMNMNNMN],oDoDOOOODODODOooOoD,Oo00oo00000O0OooOO0O00O0O)
            locals()[JIJLJJLJJJJLJILJLJJ]=WWXXWWWXWWXXWWXWXXX
        elif locals()[WWXWWWWXXWWXXWWWWWW]==wwwwwwxwxxxxwxxwxwwxx:
            locals()[liliijliillllliji]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[jilljljlljljiiljiljjjjil],JJILLILLIIIJLILJLLL,DODoOoDOOoDDOoDOD)
            locals()[MNNNMMNNMNMMNNNMMNNMNMM]=jljjllljijjjiiijjiilllljl
        elif locals()[nmmmmnnmmnnmmmmnnnnm]==xwwxwxwxxwxwwxxwwx:
            locals()[S2SS2222SS22222S22S]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[LJJILILILIIIJIJJLILJLJI],OOooDooDDDDDOOOOOOO,ODoooDoODDDDOODoODooOOo)
            locals()[NMNMMNNNNNMNNNMNNMMN]=SSSSS2SS2S2S2S2222SS
        elif locals()[lIIllIIllIIIIlllllllllll]==NNMNNNMNMNNNMNNNNMMNMMMM:
            locals()[IIIlIIIllIllIlIIlllIllII]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[IIIlIllIIIIlIllIllI],IIlllIIIIIIlIIllIlI,WWXWWWXWWWWWXWXWW)
            locals()[LJJILLLJILILJJIJIJLLLJJI]=IlIIlIlllIIIIIlIIlIlIlI
        elif locals()[OooO0ooOOOO0o000Oo0OOo0OOo]==OO0oOoo0o0Oo0oOoOO00:
            locals()[OOOOoooo0oO0OOooOo]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[S22SS2S2SSSS222S2222S222S],mmnnmnmnmmnmmmnnmmmmmn,OOOo0ooooOOoooOo0oo0o0O)
            locals()[oODOOOOoooDoDoOOoDoOoOD]=XXWWWXWXWWWXWXWXXWXXXXWW
        elif locals()[xxwwxwwxwxxwxwwwxxwxwxwwx]==oODOoDooooOooDooDD:
            locals()[XWWWWWWWXXXXXWXXX]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[DOoDOoODoODDoDDOo],S22S22SSSS2SS222SS2,mmnmmnmmnmmmmmnmmmnnnmmmm)
            locals()[XXXWXWXWXXWWWXXXXWXWWXXX]=NNMNNMMMNNNMMMMNMNNNNNMMN
        elif locals()[wxxwwwwxxxxxxxxwx]==MNMNMNNMNNMNNNMNMMMMNM:
            locals()[llIlIIllIIIllIIllI]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[nnmnmmnmmnnnnmnnmmnnmmmmm],xxwwwwxxwwxxxxwxxwwwwwwx,XWXXXWWWXXWWXXXWXWWWWXXX)
            locals()[S22S2SS22S22SSSSSS]=OOoo0Ooo0o0o00OO0oOOO0
        elif locals()[lllIIllIIlIllIlII]==xxxxxwxwxxxxxwwxx:
            locals()[jiiijliiiiljijijl]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[lIlIlIIlIlIIIlIlIIIl],MNMMNNNNMNMMMNMNNMNM,jiilljiijiiilllilljiji)
            locals()[xwwxxwxxwwxwxwwxwxwwwxxw]=JJLIJJJJJJLLLLJJJIIJII
        elif locals()[SS22222SSS2SSS22S2]==S2SSS2SS22S2S2222S22S2:
            locals()[NMMMMMNNNNMMNMNNNNMMMMMNN]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[MMMNMMNNNNMMMNNNMNNMMMN],WXXXXXWXXWWWWWWWWWWX,MMNNNNMMMNNMMMNNN)
            locals()[lljliiiilijjiiiijijilljj]=xwwwwwwxxwwxwxwwwxxwwwxxx
        elif locals()[Oooo0oOO0oOOoOO0ooo0o]==SSS222S222S2SSSSS222:
            locals()[OOoOo0000oO00o0OoOOoOo]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[mnmnmnmmmnnmmnnmmmnnmmn],O000o0OO0OO0OOo0O0o,ODOoOODDOoOODDODoDoDoo)
            locals()[mmnnmmmmmnnnnnmnmmnmnnm]=mmnnnnnmmmnmnnmnmmnmnmn
        elif locals()[XWXWXWXWXWXXXXXWXXXXXW]==IIILJLLLLILJIJIILILJI:
            locals()[WXWWWXWWWWXXWWXXXXXXWXWX]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[mnmnmmmnmmnmnmnmnmm],IlIIlIllIlllIlIIlIIIIlIlI,SS2S222222SSS2SS22)
            locals()[MMMMNNMNNNMMNMMMN]=OO00O0Oo0OO0Ooo0o0oOO00O00
        elif locals()[O0ooOoOOO0ooOoOOOoo]==xwxxwxwxxxxxwxwxxxxwx:
            locals()[NMMMMMMMMNNMNNMMMMMMNN]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[S2SS2S222S222S22S222SSS222],nmmnmnmnnnnnnnmmnnmmm,LILJLLLLJIJJLIJJJJJIJ)
            locals()[mnnnmmnmnmmnnnnnnmnn]=IIlIlIIIlllIlIIll
        elif locals()[mnnmnmmmnnnmnnnmnn]==IIlIlllIlIIlIIIIIllllIIlI:
            locals()[WWWXXWWXXWWXXWXWWXWXXWXW]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[nnnmnmmnnnmnmmnmnm],O000oO00O00000oOO0o0,nmmnmmnmnnnmnmmnmnmnmmn)
            locals()[IJLLLLIJJLJLILLJLJIIILI]=llllllllIlIIIllIIIIIlIl
        elif locals()[wxwwwxxwwwxxxxwxx]==JIIIJLILJIIJIILLJJILJL:
            locals()[nmnnnnmmnnnmmmmnmmmmmn]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[XWXXXXWWWXWXXXWWWXW],ijlijiijllljjjjjj,S2SSS2SS22S2S2S2S2)
            locals()[nnnnmmnmmnmmnmnmnm]=LLILLJIJLLILJJLJILJI
        elif locals()[JIIJJIJILLJJJIIIILJIILI]==DooDOODDDoOODDDoDOOOoDO:
            locals()[WXWWXWXWWWXXWXXXXWWWWXX]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[lllIIIlIIIlIllllIIlIlI],iijiiljljijjjlljj,SS2222S2SS222SS2222SS2SS)
            locals()[SS2S2SS22S2S2S22SSSS]=S22SS222S222S222SS2
        elif locals()[MNMNMMMNNNNNNNNNMNMNNM]==LJJJLLLIJLLIJJLJIJJIILJ:
            locals()[XWXXXWWXXWWWWWXWX]=nmnmnnnmmmnmnnnnmmmmmnnnn(locals()[IIllIllIllIlIlIlIlIIlllll],lIlIIlIlIlIlIIllIIIlIl,nmnnmmmmnmmmmnmmmnmnm)
            locals()[XXXXWXWXWXXXXXWWWXX]=NMMNMNMNNMMMMNMMMMMMNMNNN
        elif locals()[IIllIllIllIlIIlllI]==NMMNNMMMNNMNMNMNNMNMNNN:
            locals()[IlIIlllIIIlIIIIIIllII]=nmnmnnnmmmnmnnnnmmnmmnnnn(locals()[oODDooDoOOOoDODoDoODooD],IJILIIJJJJLLILIILJLI,JIIILLLJJJJJJJILJJJJLLII)
            locals()[MNMMNNMMNMMMNMMNMNN]=S2S2SS222S2SS222SS2
        elif locals()[IIllIllIIIIlIIIIIllI]==mmmnnmmmmmnmmnnnmmmnmnm:
            return
def main():
    if len(sys.argv)<=LIJIIILJLJJILIILLILJL:
        print(S22222S22S2SSS2S22SS2S22S2)
        exit(Oo00ooO0OOO00Oo0O0)
    locals()[SSS22SS222S222SSS2S]=sys.argv[DoOoODOoooDOoODoD]
    locals()[oDDDoOOoooOOoooOoODDO]=len(locals()[wxxwxwxxxxxwwxxxwxwxwxww])
    if locals()[S2222SSS2SSS22222S]<IIlIllIIlIlIIIlIIl:
        print(ODOOOoDDDDOOoooDo)
        exit(IIILLJIIIJIIJJLIJIJLJLILI)
    SS2SS2S22S22SSSSSS2SS22S2S(locals()[lljlililiiljliiij])
    locals()[S2S2SS222S22S222S22SSSS]=zlib.compress(locals()[mnmmmnnmnmnnmnnmmmmmmm].encode(O00Oo0OO00OOOOoo00OooOo0O))
    locals()[LJLJJLJIJIIJILLJJ]=len(locals()[OoO0O000000ooo0oOo0ooOO0O0])
    if locals()[xwwxxxwxxxxwwxwwxww]<wwxwxwxxwxwxxwxxwwwwx:
        print(WWWXXWXWXWWXWXWWXWXXWX)
        exit(ljijlljjiiiljjljjjiji)
    SS2SS2S22S22SSSSSS22S22S2S(locals()[SS2SS2SS22S222SSSS22SSS2])
    if locals()[SSSS222S22SS2222SS2S2S]==OO0oOO00oOo0O000oo0OOO0:
        print(XXWWWWXXWWWWWXWXW)
    else:
        print(nmnmnmnnnnmnnmnmnmmnnm)
main()
```
We see something familiar. From `Meaning of Python 1`, we know these two functions do not really change the flag, so we only have to find the cipher and decode it with zlib.

So where's the cipher? Do we really have to look over all the highly-obfuscated definitions?

No. Since all of them are just definitions, just run them in an interactive terminal and use `vars()` to see their runtime values.

With a little knowledge of zlib format, we search for bytes begin with `b'x\x9c'`:

```py
>>>[print(i) for i in vars()]
......
('OO0oOO00oOo0O000oo0OOO0', b'x\x9c\xcb,\xca,N.I\xab\xce\xa8,H-\xca\xcc\xcf\x8b7,\x8e\xcf3(\x89O\x8c/3.\xaa\x8cO70H\x897HJ+5M6)1(R\xac\x05\x00\xce\xff\x11\xdb')
......
```
decompress it with zlib again, and you get the flag:
```
irisctf{hyperion_1s_n0t_a_v3ry_g00d_0bfu5c4t0r!}
```