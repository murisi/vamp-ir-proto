e(x, y) :- x=0, y=1.
e(x, y) :- x=1, y=2.
e(2, 3).
a(x) :- x=1.
%e(2, 3).
%t(x, y) :- e(x, y).
t(x, z) :- a(y), e(x, y), e(y, z).
%t(x, y) :- -(x+y) != z.
%t(c, 2)?
square(y, x) :- y = x*x.
pyt(x, y, z) :- square(a, x), square(b, y), square(c, z), a + b = c.
pyt(x, y, z) :- x + y = z.
pyt(x, y, z)?
