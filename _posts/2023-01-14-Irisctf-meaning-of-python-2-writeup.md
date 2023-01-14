---
title: IrisCTF writeup for Meaning of Python 2
category: [Writeup, Contests] 
tags: [reverse, python, ctf]
---
# Challenge
[python2.py]({% link /assets/files/python2.py %})
# Solution
With the syntax highlighting, we can see that there is a huge byte literal(begin with `b'`), meaning that this may be the core content of the program.

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
        ...... # omitting similar paragraphs
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
        ...... # omitting similar paragraphs
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

With a little knowledge of zlib format, we search for string begin with `b'x\x9c'`:

```py
>>>[print(i) for i in vars()]
......
('OO0oOO00oOo0O000oo0OOO0', b'x\x9c\xcb,\xca,N.I\xab\xce\xa8,H-\xca\xcc\xcf\x8b7,\x8e\xcf3(\x89O\x8c/3.\xaa\x8cO70H\x897HJ+5M6)1(R\xac\x05\x00\xce\xff\x11\xdb')
......
```
decompress it with zlib again, and we get the flag:
```
irisctf{hyperion_1s_n0t_a_v3ry_g00d_0bfu5c4t0r!}
```