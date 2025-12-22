# pre: y >= 0
# post: z == x * y

z = 0
count = 0

# inv: z == x * count and count <= y
while count < y:
    z = z + x
    count = count + 1
