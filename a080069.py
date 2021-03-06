#!/usr/bin/python
############################################################################
#                                                                          #
#  http://www.research.att.com/~njas/sequences/a080069.py.txt              #
#                                                                          #
#  Coded by Antti Karttunen (His-firstname.His-surname@gmail.com),         #
#  August-September 2006.                                                  #
#                                                                          #
#  This file contains the Python-functions that compute the sequences      #
#  A080069, A080070, A122229, A122232, A122235, A122239, A122242, A122245  #
#  A179755, A179757,  A125974, A165471, A179416-A179418,                   #
#                             found in                                     #
#     Neil Sloane's On-Line Encyclopedia of Integer Sequences (OEIS)       #
#                            available at                                  #
#                          http://oeis.org                                 #
#                                                                          #
#  Copy of THIS source file is also available at:                          #
#  http://www.iki.fi/kartturi/matikka/Nekomorphisms/a080069.py             #
#                                                                          #
#  This Python-code is in Public Domain and runs (at least)                #
#  in Python 2.4.2 (#67, Sep 28 2005, 12:41:11)                            #
#  (See www.python.org)                                                    #
#                                                                          #
#  For drawing images, you need also PIL-libary,                           #
#  (tested with version 1.1.5, on Python 2.4.)                             #
#  See: http://www.pythonware.com/library/pil/handbook/index.htm           #
#                                                                          #
#  Edited  Nov 13 2012 by Antti Karttunen.                                 #
#  (Added gen_from_bfile routine for drawing A218776 - A218782 via bfiles) #
#                                                                          #
#  Edited 2019 10 05 by karttu (new 1D CA related sequences: A327971 etc   #
#                                                                          #
#                                                                          #
############################################################################

from math import *
import re

def A000120(n):
  '''Number of 1-bits in the binary expansion of n.'''
  i = 0
  while 0 != n:
    i += (n&1)
    n >>= 1
  return(i)


# floor(log(n)/log(2)) does not return correct results after n grows over certain limit!

def A000523(n):
  '''Log_2(n) rounded down. We return -1 for n=0, although -infinity would be correct.'''
  i = -1
  while 0 != n:
    i += 1
    n >>= 1
  return(i)

def A007088(n):
  '''Converts n to binary form. Or equally: nth decimal number using no other digits than 0 and 1.'''
  if 0 == n: return(0)
  else: return((n%2)+10*A007088(n/2))

# Note that A057548(n) = A080300(A057547(n)) = A080300(A079946(A014486(n)))

def A079946(n):
  '''Surround n's binary expansion with 1...0. Result's binary expansion of n has form 11**...*0.'''
  return(2*((1<<(1+A000523(n)))+n))


# Actually, the next function is A036044: write in binary, complement, reverse.
# and A057164(n) = A080300(A036044(A014486(n))) = A080300(A056539(A014486(n)))

# For these routines in C, see http://www.research.att.com/~njas/sequences/a089408.c.txt


def A030101(a):
  '''Reverse a's binary expansion.'''
  b = 0
  while 0 != a:
     b <<= 1
     b |= ((a)&1)
     a >>= 1
  return(b)


def A036044(a):
  '''Reverse and complement a totally balanced binary string.'''
  b = 0
  while 0 != a:
     b <<= 1
     b |= ((~a)&1)
     a >>= 1
  return(b)


def A000265(n):
  '''Largest odd divisor of n; or odd part of n.'''
  if 0 == n: return(n)
  while 0 == (n%2): n >>= 1
  return(n)

def A006519(n):
  '''Highest power of 2 dividing n: 1,2,1,4,1,2,1,8,1,2,1,4,1,2,1,16,...'''
  if 0 == n: return(n)
  p = 1
  while 0 == (n%2):
    n >>= 1
    p <<= 1
  return(p)

def A007814(n):
  '''Exponent of highest power of 2 dividing n (the binary carry sequence).'''
  if 0 == n: return(n)
  p = 0
  while 0 == (n%2):
    n >>= 1
    p += 1
  return(p)

def A036987(n):
  '''Fredholm-Rueppel sequence. a(n)=1 iff n = 2^m - 1.'''
  if 0 == (n & (n+1)): return(1)
  else: return(0)


def jacobi_symbol(p,q):
  '''Compute the jacobi symbol J(p/q)'''
  s = 0
  while (p > 1):
    if(p&1):
# If both p & q are 3 mod 4, then sign changes, otherwise stays same:
      s ^= (p&q) # Only the bit-1 is significant, others are ignored.
      new_p = q % p
      q = p
      p = new_p
    else:
# We have an even p. So (2k/q) = (2/q)*(k/q) 
# where (2/q) = 1 if q is +-1 mod 8 and -1 if q is +-3 mod 8.
# I.e. sign changes only if q's lower bits are (011) or (101),
# i.e. if the bit-1 and bit-2 xored yield 1.
      s ^= (q^(q>>1))      # Thus, this does it.
      p >>= 1

  if(0==p): return(p)
  else: return(1-(s&2)) # p=1


def A165471(n):
  '''Legendre symbol L(n/65537).'''
  return(jacobi_symbol(n,65537))

def oneplushalved(n): return((n+1)/2)

def A179416(n): return(oneplushalved(A165471(1+(n%65536))))

def A179417(n):
  ul = 1+(2*n)
  i = n*n
  j = 0
  s = 0
  while j<ul:
    if(1==oneplushalved(A165471(1+i))): s += 2**j
    i += 1
    j += 1

  return(s)


def A179418(n): return(A000120(A179417(n)))


## Note: A125974(10) should return 12, not 4!
def A125974(n):
  '''Function whose restriction to A014486 induces Kreweras bijection A125976.'''
  if 0 == n: return(n)

  chosen = A000265(n)         # Initially ones, get rid of lsb-0's.
  others = n >> A007814(n+1)  # Initially zeros, get rid of lsb-1's.
  s = 0     # the resulting sum
  b = n%2   # n's parity.
  p = 1     # powers of two.

  while (chosen != 0) or (others != 0):
    if (1 == chosen) or (1 == A036987(chosen+1)):  # Last one or zero at hand.
       chosen = others
       others = 0
       nb = 1 - b
    elif (0 == (chosen%4)) or (3 == (chosen%4)):   # Source run continues, dest changes.
       tmp = chosen
       chosen = others
       others = tmp >> 1
       nb = 1 - b
    elif (1 == (chosen%4)): # Source run changes, from ones to zeros, skip past zeros.
       chosen = A000265(chosen-1)
       nb = b
    else: # i.e. if (2 == (chosen%4)) source run changes, from zeros to ones, skip past ones.
       chosen = chosen >> A007814(chosen+2)
       nb = b

    s += b*p
    p <<= 1
    b = nb

  return(s)


def tb_A057164(a):
  return(A036044(a))

def tb_A057163(a):
  '''Reflect a binary tree represented as a totally balanced binary string.
     Keep two "parallel" stacks, the other for the reconstructed
     totally balanced binary strings, and the other for their
     corresponding sizes.
     Start scanning the argument "a" from the end, pushing
     zeros (leaves) to the stack, and joining to topmost
     subtrees (-binary strings) popped from the stack
     when 1 is encountered.'''


  tree_stack = [0] # The last leaf is implicit, not marked in a.
  size_stack = [1] # And its size is 1.

  while (0 != a):
     if(0 == (a&1)): # Push zeros (leaves) to stack.
         tree_stack.append(0)
         size_stack.append(1)
     else: # It's 1, join two branches in swapped order.
         leftchild  = tree_stack.pop()
         rightchild = tree_stack.pop()
         leftsize   = size_stack.pop()
         rightsize  = size_stack.pop()

         size_stack.append(1+leftsize+rightsize)
         tree_stack.append((1 << (leftsize+rightsize)) + (rightchild << leftsize) + leftchild)
     a >>= 1

  return(tree_stack.pop() >> 1) # Discard the last leaf by halving.


def tb_A057117_aux(n,i,r):
  '''Apply the gatomorphism A057117 to A014486-codes. Aux. function that does most of the work.'''

  if(0 == ((n)&1)): return(0)

  c = i
  j = 1
  while j <= r:
     c += (n & 1)
     n >>= 1
     j += 1

  w = c << 1  # w = 2*c
  i <<= 1     # i = 2*i

# Now w = twice the count of ones on preceding row, the width of the next one.
# n points to the beginning of the next row.

  c = 0
  j = 1
  while j <= i:
     c += (n & 1)
     n >>= 1
     j += 1

# Now the 1-bit at the beginning of n is "c":th 1 in whole n (zero-based).

  x = tb_A057117_aux(n,c,(w-(j-1)))
  y = tb_A057117_aux(n>>1,c+(n&1),(w-j))

  if(0 == y): ywidth = 1
  else: ywidth = A000523(y)+1

  if(0 == x): xwidth = 1
  else: xwidth = A000523(x)+1

  return((1 << (ywidth+xwidth)) + (x << ywidth) + y)


def tb_A057117(a):
  '''Apply the gatomorphism A057117 to A014486-codes.'''
  return(tb_A057117_aux(A030101(a),0,1) >> 1)




def tb_A082356(a):
  '''Implement the gatomorphism A082356 on A014486-codes.
     Keep two "parallel" stacks, the other for the reconstructed
     totally balanced binary strings, and the other for their
     corresponding sizes.
     Start scanning the argument "a" as base-4 number, from the
     least-significant end, ...
     See the function quatexpA->parenthesization in gatorank.scm
     and http://www.research.att.com/~njas/sequences/A085184'''

  if(0 == a): return(a)

  a >>= 1 # Discard the least-significant bit (0) before starting.

  tree_stack = [4] # The last two leaves are implicit, 100 in binary.
  size_stack = [3] # And their total size in bits is 3.


  while (a > 2):
     if(0 == (a&3)): # Double-zeros stand for double-leaves (\/), just push them to stack.
         leftchild  = 0
         leftsize   = 1
         rightchild = 0
         rightsize  = 1

     elif(1 == (a&3)): # (case 01)
         rightchild = tree_stack.pop()
         rightsize  = size_stack.pop()
         leftchild  = 0
         leftsize   = 1

     elif(2 == (a&3)): # (case 10)
         rightchild = 0
         rightsize  = 1
         leftchild  = tree_stack.pop()
         leftsize   = size_stack.pop()

     else: # It's 3 (case 11), join two branches in normal order.
         leftchild  = tree_stack.pop()
         leftsize   = size_stack.pop()
         rightchild = tree_stack.pop()
         rightsize  = size_stack.pop()

     size_stack.append(1+leftsize+rightsize)
     tree_stack.append((1 << (leftsize+rightsize)) + (leftchild << rightsize) + rightchild)

     a >>= 2 # Next digit in base-4.

  return(tree_stack.pop() >> 1) # Discard the last leaf by halving.



def tb_A074684(a):
  '''Implement the gatomorphism A074684 on A014486-codes. A variant of above.'''

  if(0 == a): return(a)

  a >>= 1 # Discard the least-significant bit (0) before starting.

  tree_stack = [4] # The last two leaves are implicit, 100 in binary.
  size_stack = [3] # And their total size in bits is 3.


  while (a > 2):
     if(0 == (a&3)): # Double-zeros stand for double-leaves (\/), just push them to stack.
         leftchild  = 0
         leftsize   = 1
         rightchild = 0
         rightsize  = 1

     elif(1 == (a&3)): # (case 01)
         rightchild = 0
         rightsize  = 1
         leftchild  = tree_stack.pop()
         leftsize   = size_stack.pop()

     elif(2 == (a&3)): # (case 10)
         rightchild = tree_stack.pop()
         rightsize  = size_stack.pop()
         leftchild  = 0
         leftsize   = 1

     else: # It's 3 (case 11), join two branches in normal order.
         leftchild  = tree_stack.pop()
         leftsize   = size_stack.pop()
         rightchild = tree_stack.pop()
         rightsize  = size_stack.pop()

     size_stack.append(1+leftsize+rightsize)
     tree_stack.append((1 << (leftsize+rightsize)) + (leftchild << rightsize) + rightchild)

     a >>= 2 # Next digit in base-4.

  return(tree_stack.pop() >> 1) # Discard the last leaf by halving.



def tb_A082358(a):
  '''Implement the gatomorphism A082358 on A014486-codes. A variant of above.'''
  return(tb_A057163(tb_A082356(a)))

def tb_A082360(a):
  '''Implement the gatomorphism A082360 on A014486-codes. A variant of above ones.'''
  return(tb_A057163(tb_A074684(a)))


# (same-intfuns? A082358 (compose-funs A057163 A057117) 2055) --> 56
# I.e., are up to n=55 identical. Let's use that fact...

def tb_Anewgm1(a):
  '''Implement a new Cat. bijection on A014486-codes.'''
  return(tb_A057163(tb_A057117(a)))


########################################################################

# For testing:

seqA014486 = [0,2,10,12,42,44,50,52,56,170,172,178,180,184,202,
              204,210,212,216,226,228,232,240,682,684,690,692,
              696,714,716,722,724,728,738,740,744,752,810,812,
              818,820,824,842,844,850,852,856,866,868,872,880,
              906,908,914,916,920,930,932,936,944,962,964,968,976,992]

# For example:
# l = [tb_A057117(n) for n in seqA014486]
# [seqA014486.index(l[i]) for i in range(len(l))]
# Gives the signature-permutation of A057117:
# [0, 1, 2, 3, 4, 5, 7, 8, 6, 9, 10, 12, 13, 11, 17, 18, 21, 22, 20, 14, 15, 16, 19, 23, 24, 26, 27, 25, 31, 32, 35, 36, 34, 28, 29, 30, 33, 45, 46, 49, 50, 48, 58, 59, 63, 64, 62, 54, 55, 57, 61, 37, 38, 40, 41, 39, 44, 47, 42, 43, 56, 60, 51, 52, 53]

# l = [tb_A082356(n) for n in seqA014486]
# [seqA014486.index(l[i]) for i in range(len(l))]

# l = [tb_A082358(n) for n in seqA014486]
# [seqA014486.index(l[i]) for i in range(len(l))]

# l = [tb_A082360(n) for n in seqA014486]
# [seqA014486.index(l[i]) for i in range(len(l))]

# l = [tb_A074684(n) for n in seqA014486]
# [seqA014486.index(l[i]) for i in range(len(l))]

########################################################################


def gen_from_bfile(filename):
  '''Yield successive terms from b-file "filename".'''
  def bfilegenerator():
      infp = open(filename,'r')
    
      linepat = re.compile(r'^([0-9]+) ([0-9]+)')
    
      terms = ""
    
      for line in infp.xreadlines(): 
        m = linepat.match(line)
        if(m):
          ind  = m.group(1) #
          val  = m.group(2) #
          yield int(val);
        else:
          print "SKIPPING THE FOLLOWING LINE in " + filename + ": " + line + "\n"
    
      yield(-1)

  return(bfilegenerator)

# End of gen_from_bfile function.


def take(n,g):
  '''Returns a list composed of n next elements returned by generator g. Inspired by Haskell'''
  z = []
  if 0 == n: return(z)
  for x in g:
    z.append(x)
    if n > 1:
      n = n-1
    else:
      return(z)


# Note that A080068 can be also obtained as iteration of A072795 o A057506.
# This works as A057506(n) = A057163(A057164(n), and instead of adding a right stick ./
# to the binary tree at the middle, we can add a left stick \. into it in the beginning
# or at the end of each iteration.

# E.g. take(10,genA080069()) gives: [2, 10, 44, 178, 740, 2868, 11852, 47522, 190104, 735842]

def genA080069():
    '''Yield successive terms of A080069, starting from A080069(1)=2.'''
    i = 2
    while True:
       yield i
       i = tb_A057163(A079946(tb_A057164(i)))

def genA080070():
    '''Yield successive terms of A080070, starting from A080070(1)=10.'''
    i = 2
    while True:
       yield A007088(i)
       i = tb_A057163(A079946(tb_A057164(i)))


def genA122229():
    '''Yield successive terms of A122229, starting from A122229(1)=2.'''
    i = 2 # Boring to look at, but included for completeness!
    while True:
       yield i
       i = A079946(tb_A057117(i))


def genA122232():
    '''Yield successive terms of A122232, starting from A122232(1)=42.'''
    i = 42 # Chaotic...
    while True:
       yield i
       i = A079946(tb_A057117(i))


def genA122235():
    '''Yield successive terms of A122235, starting from A122235(1)=44.'''
    i = 44 # Similar looking. Should compute for starting values 50 and 52 also.
    while True:
       yield i
       i = A079946(tb_A057117(i))


def genA122239():
    '''Yield successive terms of A122239, starting from A122239(1)=52.'''
    i = 52 # Similar looking. Should compute for starting value 50 also.
    while True:
       yield i
       i = A079946(tb_A057117(i))

# Neither A082356 nor A074684 dissipate the change.
# But A082358 is surely interesting!

def genA122242():
    '''Yield successive terms of A122242, starting from A122242(1)=42.'''
    i = 42
    while True:
       yield i
       i = A079946(tb_A082358(i))


def genA122245():
    '''Yield successive terms of A122245, starting from A122245(1)=44.'''
    i = 44 # Similar looking. Should compute for starting values 50 and 52 also.
    while True:
       yield i
       i = A079946(tb_A082358(i))


def genA179755():
    '''Yield successive terms of A179755, starting from A179755(1)=50.'''
    i = 50
    while True:
       yield i
       i = A079946(tb_A082358(i))

def genA179757():
    '''Yield successive terms of A179757, starting from A179757(1)=56.'''
    i = 56
    while True:
       yield i
       i = A079946(tb_A082358(i))

def genA179417():
    '''Yield successive terms of A179417, starting from A179417(0)=1.'''
    i = 0
    while True:
       yield A179417(i)
       i += 1


# Regular, boring:
def genA1new0():
    '''Yield successive terms of A1new0, starting from A1new0(1)=2.'''
    i = 2
    while True:
       yield i
       i = A079946(tb_Anewgm1(i))


# Very chaotic, although the first four terms in both iterations
# are equal to A122242 and A122245:

def genA1new1():
    '''Yield successive terms of A1new1, starting from A1new1(1)=42.'''
    i = 42
    while True:
       yield i
       i = A079946(tb_Anewgm1(i))

def genA1new2():
    '''Yield successive terms of A1new2, starting from A1new2(1)=44.'''
    i = 44
    while True:
       yield i
       i = A079946(tb_Anewgm1(i))


def genA0new11():
    '''Yield successive terms of A0new11.'''
    i = 42
    j = 44
    while True:
       yield (i^j)
       i = A079946(tb_A082358(i))
       j = A079946(tb_A082358(j))


def genA0new12():
    '''Yield successive terms of A0new12.'''
    i = 42
    j = 50
    while True:
       yield (i^j)
       i = A079946(tb_A082358(i))
       j = A079946(tb_A082358(j))


def genA0new13():
    '''Yield successive terms of A0new13.'''
    i = 42
    j = 56
    while True:
       yield (i^j)
       i = A079946(tb_A082358(i))
       j = A079946(tb_A082358(j))


def genA0new14():
    '''Yield successive terms of A0new14.'''
    i = 44
    j = 50
    while True:
       yield (i^j)
       i = A079946(tb_A082358(i))
       j = A079946(tb_A082358(j))


def genA0new15():
    '''Yield successive terms of A0new15.'''
    i = 44
    j = 56
    while True:
       yield (i^j)
       i = A079946(tb_A082358(i))
       j = A079946(tb_A082358(j))

def genA0new16():
    '''Yield successive terms of A0new16.'''
    i = 50
    j = 56
    while True:
       yield (i^j)
       i = A079946(tb_A082358(i))
       j = A079946(tb_A082358(j))




# Ah, Pyramids are here again! (Keep this!)
def genA0new3():
    '''Yield successive terms of A0new3, starting from A0new3(1)=2.'''
    i = 2
    while True:
       yield i
       i = A079946(A125974(i))

# Keep this! Why the funny checker-board pattern when non-zoomed?
# (it's an artefact of PNG-display routine, most probably!)
def genA0new4():
    '''Yield successive terms of A0new4, starting from A0new4(1)=2.'''
    i = 2
    while True:
       yield i
       i = A079946(tb_A057163(A125974(tb_A057163(i))))

# Maybe this also.
def genA0new5():
    '''Yield successive terms of A0new5, starting from A0new5(1)=2.'''
    i = 2
    while True:
       yield i
       i = tb_A057163(A079946(A125974(tb_A057163(i))))

# Something like 1D "gliders":
def genA0new6():
    '''Yield successive terms of A0new6, starting from A0new6(1)=44.'''
    i = 44
    while True:
       yield i
       i = A125974(A079946(tb_A057163(i)))

def genA0new7():
    '''Yield successive terms of A0new3, starting from A0new3(1)=2.'''
    i = 44
    while True:
       yield i
       i = A079946(A125974(i))

def genA0newX():
    '''Yield successive terms of A0new1, starting from A0newX(1)=2.'''
    i = 2 # Very regular, like some class-1 1D-CA.
    while True:
       yield i
       i = A079946(tb_A082360(i))

#
# One-dimensional cellular automata
#

def A048727(n): return(n^(n<<1)^(n<<2))

def A269160(n):
    '''Formula for Wolfram's Rule 30 cellular automaton: a(n) = n XOR (2n OR 4n).'''
    return(n^((n<<1)|(n<<2)))

def A269161(n):
    '''Formula for Wolfram's Rule 86 cellular automaton: a(n) = 4n XOR (2n OR n).'''
    return((n<<2)^((n<<1)|n))

def A269174(n):
    '''Formula for Wolfram's Rule 124 cellular automaton: a(n) = (n OR 2n) AND ((n XOR 2n) OR (n XOR 4n)).'''
    return((n|(n<<1))&((n^(n<<1))|(n^(n<<2))))


def genA038184():
    '''Yield successive terms of A038184, 1, 7, 21, 107, 273, 1911, ... (Rule 150) starting from A038184(0)=1.'''
    s = 1
    while True:
       yield s
       s = A048727(s)


def genA110240():
    '''Yield successive terms of A110240 (Rule 30) starting from A110240(0)=1.'''
    s = 1
    while True:
       yield s
       s = A269160(s)

def genA265281():
    '''Yield successive terms of A265281 (Rule 86), starting from A265281(0)=1.'''
    s = 1
    while True:
       yield s
       s = A269161(s)

def genA267357():
    '''Yield successive terms of A267357 (Rule 124), starting from A267357(0)=1.'''
    s = 1
    while True:
       yield s
       s = A269174(s)


def genA327971():
    '''Yield successive terms of A327971, 0, 0, 10, 20, 130, 396, 2842, ...: a(n) = A110240(n) XOR A265281(n).'''
    s1 = 1
    s2 = 1
    while True:
       yield (s1^s2)
       s1 = A269160(s1)
       s2 = A269161(s2)


def genA327972():
    '''Yield successive terms of A327972, 0, 0, 12, 4, 128, 384, ...: a(n) = A110240(n) XOR A038184(n).'''
    s1 = 1
    s2 = 1
    while True:
       yield (s1^s2)
       s1 = A269160(s1)
       s2 = A048727(s2)


def genA327973():
    '''Yield successive terms of A327973, 5, 23, 93, 335, 1493, 5351, ...: a(n) = A110240(n) XOR 2*A110240(n-1).'''
    s = 1
    while True:
       t = A269160(s)
       yield (t^(s<<1))
       s = t


def genA327976():
    '''Yield successive terms of A327976, 5, 23, 73, 359, 1233, ...: a(n) = A110240(n) XOR 2*A265281(n-1).'''
    s1 = 1
    s2 = 1
    while True:
       s1 = A269160(s1)
       yield (s1^(s2<<1))
       s2 = A269161(s2)


def genA328104():
    '''Yield successive terms of A328104, 3, 15, 59, 255, 947, ...: a(n) = A163617(A110240(n)) = A110240(n) OR 2*A110240(n).'''
    s = 1
    while True:
       yield (s|(s<<1))
       s = A269160(s)


def genA328103():
    '''Yield successive terms of A328103 (= A110240(n) XOR A267357(n)).'''
    s1 = 1
    s2 = 1
    while True:
       yield (s1^s2)
       s1 = A269174(s1)
       s2 = A269160(s2)
#      s1 = (s1^(4*s1))
#      s2 = A079946(tb_A082358(s2))
#      s2 = tb_A057163(A079946(tb_A057164(s2)))

def genA328111():
    '''Yield successive terms of A328111 (= A080069(n) OR A267357(n)).'''
    s1 = 1
    s2 = 0
    while True:
       yield (s1|s2)
       s1 = A269174(s1)
       s2 = tb_A057163(A079946(tb_A057164(s2)))

       
########################################################################
#
#
# Part for drawing the above sequence in "Wolframesque 1D-CA manner".
#
# C.f. also Symbolic Systems in chapter 3 "The World of Simple Programs"
# in Stephen Wolfram, A New Kind of Science, Wolfram Media, 2002;
# pp. 102-104, 896-898
#
#
########################################################################

# Uses the PIL-libary, version 1.1.5, on Python 2.4.
# See: http://www.pythonware.com/library/pil/handbook/index.htm
# The graphics interface uses the same coordinate system as PIL itself,
# with (0, 0) in the upper left corner.
# Can be installed in Ubuntu with shell command pip install Pillow
# (and with sudo apt install python-pip before that, if needed)

from PIL import Image, ImageDraw, ImageFont

def draw_point(draw,x,y,scale,color):
  pixrange = range(scale)
  for x_off in pixrange:
    for y_off in pixrange: draw.point([(x-x_off,y+y_off)], fill=color)



def draw_bin_string(draw,row,scale,width,height,ymargin,binstr):
  x = (width-1) - ( (width-scale*(A000523(binstr)+1)) / 2 ) # Get it into center.
# x = (width/2) + (scale*row) - 1 # Simpler!
  y = scale*(row - 1) + ymargin
  black = (0,0,0)
  white = (256,256,256)
  pixrange = range(scale)
  while 0 != binstr:
    if (1 == (binstr%2)): color = black # 1's are black.
    else:                 color = white # 0's are white.
    draw_point(draw,x,y,scale,color)
    binstr >>= 1
    x -= scale


def draw_up_to_n(gen,upto_n,scale,filebase,captext):
  '''Draw binary strings produced by generator gen, up to upto_n:th row, saving
     the image to the file, with additional caption "captext", if present.'''

  bfileout = open("b"+filebase+".txt",'w')

  row = 1
  xmargin = 0
  ymargin = 1


# Take the first integer returned by the generator gen:
  for binstr in gen:
    bfileout.write(str(row)+" "+str(binstr)+"\n")
    break

  firstwid = (A000523(binstr)+1)

  width  = 2*(scale*upto_n) + (scale*firstwid) + 2*xmargin
  height = (scale*upto_n) + 2*ymargin
  image = Image.new("RGB",(width,height),(128,000,000)) # Nice red background
# image = Image.new("RGB",(width,height),(000,128,000)) # Nice toxic green background
  draw = ImageDraw.Draw(image)
  draw_bin_string(draw,row,scale,width,height,ymargin,binstr)

  row += 1

# x = (width-1) - (width-(A000523(binstr)+1))/2 # Get it into center.

# And then the rest:
  for binstr in gen:
    bfileout.write(str(row)+" "+str(binstr)+"\n")
    draw_bin_string(draw,row,scale,width,height,ymargin,binstr)
    row += 1
    if row > upto_n: break

  bfileout.close()

  if(captext):
    # font = ImageFont.load("some_larger_font.pil") # But we don't have it!
    font = ImageFont.load_default()
    draw.text((10,10), captext, fill=(0,0,0), font=font) # Text in black.
    draw.text((10,25), "First "+str(upto_n)+" terms, 1 bit = "
                       + str(scale) + "x" + str(scale) + " pixels.",
                       fill=(0,0,0), font=font)

  del draw
  image.save("a" + filebase + "_" + str(upto_n) + ".png","png")

########################################################################



def draw_binseq_from_bfile(filebase,firstwid,scale,captext):
  '''Draw a binary triangle based on b-file containing just 0's and 1's
     drawing the first firstwid bits centered on the top row,
     and after that two bits more on each row.
     Save the image to the file, with additional caption "captext".'''

  black = (0,0,0)
  white = (256,256,256)

  try:
    bfilein = open("b"+filebase+".txt",'r')
  except IOError: # There were no edit-file present.
    return(None)

# First count how many rows the input-file contains terms for:
  widthnow = firstwid
  w = widthnow
  rows = 0

  for line in bfilein.xreadlines(): 
    w -= 1
    if(0==w):
      widthnow += 2
      w = widthnow
      rows += 1

  bfilein.seek(0) # Rewind back to beginning.

  upto_n = rows

  xmargin = 0
  ymargin = 1

  width  = 2*(scale*rows) + (scale*firstwid) + 2*xmargin
  height = (scale*rows) + 2*ymargin
  x_start = (width/2) - (scale*(firstwid/2))

  print 'Drawing image of width x height ' + str(width) + 'x' + str(height) + ' pixels. ' + str(rows) + ' rows, first row is ' + str(firstwid) + ' bits, x_start = ' + str(x_start) + '\n'

# image = Image.new("RGB",(width,height),(128,000,000)) # Nice red background
  image = Image.new("RGB",(width,height),(000,000,128)) # Nice blue background
  draw = ImageDraw.Draw(image)

  widthnow = firstwid
  w = widthnow

  linepat = re.compile(r'^([0-9]+)\s+([0-9]+)')

  y = ymargin
  x = x_start

# Then read the bfile in again:
  for line in bfilein.xreadlines():
    m = linepat.match(line)
    if(m):
      lineno = int(m.group(1))
      bit    = int(m.group(2))
      if(0 == bit): color = white # 0's are black.
      else:         color = black # 1's are white.

      draw_point(draw,x,y,scale,color)

      w -= 1
      if(0==w): # Time to change to the next row?
        widthnow += 2 # It's two bits wider
        w = widthnow
        y += scale    # Towards bottom of the screen...
        x_start -= scale # And the next row one block more left
        x = x_start
      else:
        x += scale

    else:
      print 'Comment-line or ill-formed, skipping: ' + line + '\n'
      continue

  bfilein.close()

  if(captext):
    # font = ImageFont.load("some_larger_font.pil") # But we don't have it!
    font = ImageFont.load_default()
    draw.text((10,10), captext, fill=(0,0,0), font=font) # Text in black.
    draw.text((10,25), "First "+str(upto_n)+" terms, 1 bit = "
                       + str(scale) + "x" + str(scale) + " pixels.",
                       fill=(0,0,0), font=font)

  del draw
# image.save("a" + filebase + "_" + str(upto_n) + ".png","png")
  image.save("a" + filebase + "_p" + str(scale) + ".png","png")


########################################################################


# Very fine texture, like a pyramid of sand polished by the wind!
def do_it_for_A080069(upto_n,scale):
  draw_up_to_n(genA080069(),upto_n,scale,"080069","See: http://oeis.org/A080069")

# Boringly regular:
def do_it_for_A122229(upto_n,scale):
  draw_up_to_n(genA122229(),upto_n,scale,"122229","See: http://oeis.org/A122229")

# Chaotic:
def do_it_for_A122232(upto_n,scale):
  draw_up_to_n(genA122232(),upto_n,scale,"122232","See: http://oeis.org/A122232")

def do_it_for_A122235(upto_n,scale):
  draw_up_to_n(genA122235(),upto_n,scale,"122235","See: http://oeis.org/A122235")

# Are the "circles" real?
def do_it_for_A122239(upto_n,scale):
  draw_up_to_n(genA122239(),upto_n,scale,"122239","See: http://oeis.org/A122239")

def do_it_for_A122242(upto_n,scale):
  draw_up_to_n(genA122242(),upto_n,scale,"122242","See: http://oeis.org/A122242")

def do_it_for_A122245(upto_n,scale):
  draw_up_to_n(genA122245(),upto_n,scale,"122245","See: http://oeis.org/A122245")

def do_it_for_A179755(upto_n,scale):
  draw_up_to_n(genA179755(),upto_n,scale,"179755","See: http://oeis.org/A179755")

def do_it_for_A179757(upto_n,scale):
  draw_up_to_n(genA179757(),upto_n,scale,"179757","See: http://oeis.org/A179757")

def do_it_for_A179417(upto_n,scale):
  draw_up_to_n(genA179417(),upto_n,scale,"179417","See: http://oeis.org/A179417")


def do_it_for_A218776(upto_n,scale):
  draw_up_to_n((gen_from_bfile("b218776.upto4096.txt"))(),upto_n,scale,"218776","See: http://oeis.org/A218776")

def do_it_for_A218778(upto_n,scale):
  draw_up_to_n((gen_from_bfile("b218778.upto4096.txt"))(),upto_n,scale,"218778","See: http://oeis.org/A218778")

def do_it_for_A218780(upto_n,scale):
  draw_up_to_n((gen_from_bfile("b218780.upto4096.txt"))(),upto_n,scale,"218780","See: http://oeis.org/A218780")

def do_it_for_A218782(upto_n,scale):
  draw_up_to_n((gen_from_bfile("b218782.upto4096.txt"))(),upto_n,scale,"218782","See: http://oeis.org/A218782")


def do_it_for_A1new0(upto_n,scale):
  draw_up_to_n(genA1new0(),upto_n,scale,"800000","See: http://oeis.org/A1new0")

def do_it_for_A1new1(upto_n,scale):
  draw_up_to_n(genA1new1(),upto_n,scale,"800001","See: http://oeis.org/A1new1")

def do_it_for_A1new2(upto_n,scale):
  draw_up_to_n(genA1new2(),upto_n,scale,"800002","See: http://oeis.org/A1new2")


def do_it_for_A0new3(upto_n,scale):
  draw_up_to_n(genA0new3(),upto_n,scale,"900003","See: http://oeis.org/A0new3")

def do_it_for_A0new4(upto_n,scale):
  draw_up_to_n(genA0new4(),upto_n,scale,"900004","See: http://oeis.org/A0new4")

def do_it_for_A0new5(upto_n,scale):
  draw_up_to_n(genA0new5(),upto_n,scale,"900005","See: http://oeis.org/A0new5")

def do_it_for_A0new6(upto_n,scale):
  draw_up_to_n(genA0new6(),upto_n,scale,"900006","See: http://oeis.org/A0new6")

def do_it_for_A0new7(upto_n,scale):
  draw_up_to_n(genA0new7(),upto_n,scale,"900007","See: http://oeis.org/A0new7")

def do_it_for_A0new11(upto_n,scale):
  draw_up_to_n(genA0new11(),upto_n,scale,"900011","See: http://oeis.org/A0new11")

def do_it_for_A0new12(upto_n,scale):
  draw_up_to_n(genA0new12(),upto_n,scale,"900012","See: http://oeis.org/A0new12")

def do_it_for_A0new13(upto_n,scale):
  draw_up_to_n(genA0new13(),upto_n,scale,"900013","See: http://oeis.org/A0new13")

def do_it_for_A0new14(upto_n,scale):
  draw_up_to_n(genA0new14(),upto_n,scale,"900014","See: http://oeis.org/A0new14")

def do_it_for_A0new15(upto_n,scale):
  draw_up_to_n(genA0new15(),upto_n,scale,"900015","See: http://oeis.org/A0new15")

def do_it_for_A0new16(upto_n,scale):
  draw_up_to_n(genA0new16(),upto_n,scale,"900016","See: http://oeis.org/A0new16")

def do_it_for_A110240(upto_n,scale):
  draw_up_to_n(genA110240(),upto_n,scale,"110240","See: http://oeis.org/A110240")

def do_it_for_A267357(upto_n,scale):
  draw_up_to_n(genA267357(),upto_n,scale,"267357","See: http://oeis.org/A110240")
  
def do_it_for_A327971(upto_n,scale):
  draw_up_to_n(genA327971(),upto_n,scale,"327971","See: http://oeis.org/A327971")

def do_it_for_A327972(upto_n,scale):
  draw_up_to_n(genA327972(),upto_n,scale,"327972","See: http://oeis.org/A327972")

def do_it_for_A327973(upto_n,scale):
  draw_up_to_n(genA327973(),upto_n,scale,"327973","See: http://oeis.org/A327973")

def do_it_for_A327976(upto_n,scale):
  draw_up_to_n(genA327976(),upto_n,scale,"327976","See: http://oeis.org/A327976")

def do_it_for_A328103(upto_n,scale):
  draw_up_to_n(genA328103(),upto_n,scale,"328103","See: http://oeis.org/A328103")

def do_it_for_A328104(upto_n,scale):
  draw_up_to_n(genA328104(),upto_n,scale,"328104","See: http://oeis.org/A328104")

def do_it_for_A328111(upto_n,scale):
  draw_up_to_n(genA328111(),upto_n,scale,"328111","See: http://oeis.org/A328111")

  
########################################################################
#                                                                      #
#  For the comparison, here are Scheme-implementations of some of the  #
#  Catalan automorphisms defined above.                                #
#                                                                      #
########################################################################


# (define (*a082356! s) ;; *a082352! applied to recursion case 0.
#   (cond ((pair? s) (*a082352! s) (*a082356! (car s)) (*a082356! (cdr s))))
#   s
# )
# 
# 
# 
# ;; D   C
# ;;  \ /
# ;;   P   B         D  C B  A  []  B        B   A
# ;;    \ /           \ / \ /    \ /          \ /         and by default:
# ;;     M   A   -->   Q   N      M   A   -->  N  []     []  A       []  A
# ;;      \ /           \ /        \ /          \ /       \ /   -->   \ /
# ;;       X             Y          X            Y         X           Y
# 
# 
# (define (*a082352! s)
#   (cond ((not (pair? s)) s)
#         ((not (pair? (car s))) s)
#         ((not (pair? (caar s))) (swap! (robr! s)))
#         (else (robr! s))
#   )
# )
# 

# And relevant code from gatorank.scm

# (define (binexp->parenthesization n)
#    (let loop ((n n) (stack (list (list))))
#        (cond ((zero? n) (car stack))
#              ((zero? (modulo n 2))
#                 (loop (floor->exact (/ n 2)) (cons (list) stack))
#              )
#              (else
#                 (loop (floor->exact (/ n 2)) (cons2top! stack))
#              )
#        )
#    )
# )
# 
# 
# ;; Experimental, quaternary zigzag-tree code, variant A:
# ;; Differs from A057117 first time at position 56,
# ;; whence this has 42 while it has 44.
# ;; This is now stored in OEIS as A082356.
# ;; (map CatalanRankGlobal (map parenthesization->binexp (map quatexpA->parenthesization (map A014486 (iota0 64)))))
# ;; (0 1 2 3 4 5 7 8 6 9 10 12 13 11 17 18 21 22 20 14 15 16 19 23 24 26 27 25 31 32 35 36 34 28 29 30 33 45 46 49 50 48 58 59 63 64 62 54 55 57 61 37 38 40 41 39 42 43 44 47 51 52 56 60 53)
# 
# (define (quatexpA->parenthesization n)
#    (if (zero? n) (list)
#        (let loop ((n (floor->exact (/ n 2)))
#                   (stack (list (cons (list) (list))))
#                  )
#            (cond ((< n 2) (car stack))
#                  (else
#                    (case (modulo n 4)
#                      ((0) ;; 00
#                         (loop (floor->exact (/ n 4))
#                               (cons (cons (list) (list)) stack)
#                         )
#                      )
#                      ((1) ;; 01
#                         (loop (floor->exact (/ n 4))
#                               (cons2top! (cons (list) stack))
#                         )
#                      )
#                      ((2) ;; 10
#                         (loop (floor->exact (/ n 4))
#                               (flip!topmost (cons2top! (cons (list) stack)))
#                         )
#                      )
#                      ((3) ;; 11
#                         (loop (floor->exact (/ n 4))
#                               (cons2top! stack)
#                         )
#                      )
#                    )
#                  )
#            )
#        )
#    )
# )
# 
# ;; (map CatalanRankGlobal (map parenthesization->binexp (map quatexpB->parenthesization (map A014486 (iota0 64)))))
# ;; (0 1 3 2 8 7 5 4 6 22 21 18 17 20 13 12 10 9 11 15 14 19 16 64 63 59 58 62 50 49 46 45 48 55 54 61 57 36 35 32 31 34 27 26 24 23 25 29 28 33 30 41 40 38 37 39 52 51 60 56 43 42 47 44 53)
# ;; Is equal to A074684.
# ;; Variant B, with the roles of 01 and 10 swapped: (but 11 is not flipped!)
# (define (quatexpB->parenthesization n)
#    (if (zero? n) (list)
#        (let loop ((n (floor->exact (/ n 2)))
#                   (stack (list (cons (list) (list))))
#                  )
#            (cond ((< n 2) (car stack))
#                  (else
#                    (case (modulo n 4)
#                      ((0) ;; 00
#                         (loop (floor->exact (/ n 4))
#                               (cons (cons (list) (list)) stack)
#                         )
#                      )
#                      ((1) ;; 01
#                         (loop (floor->exact (/ n 4))
#                               (flip!topmost (cons2top! (cons (list) stack)))
#                         )
#                      )
#                      ((2) ;; 10
#                         (loop (floor->exact (/ n 4))
#                               (cons2top! (cons (list) stack))
#                         )
#                      )
#                      ((3) ;; 11
#                         (loop (floor->exact (/ n 4))
#                               (cons2top! stack)
#                         )
#                      )
#                    )
#                  )
#            )
#        )
#    )
# )
# 

# 
# ;; Convert (a . (b . rest)) --> ((a . b) . rest)
# ;; with no cons cells wasted.
# 
# (define (cons2top! stack)
#   (let ((ex-cdr (cdr stack)))
#       (set-cdr! stack (car ex-cdr))
#       (set-car! ex-cdr stack)
#       ex-cdr
#   )
# )
# 
# (define (flip!topmost stack)
#   (let* ((topmost (car stack))
#          (ex-cdr (cdr topmost))
#         )
#       (set-cdr! topmost (car topmost))
#       (set-car! topmost ex-cdr)
#       stack
#   )
# )
# 

