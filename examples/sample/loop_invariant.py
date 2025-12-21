# pre: n >= 0

i = 0
s = 0

# inv: 0 <= i <= n and 2 * s == i * (i + 1)
while i < n:
    i = i + 1
    s = s + i

# post: 2 * s == n * (n + 1)
