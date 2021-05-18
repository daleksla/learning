A = matrix(c(4,2), nrow=1, ncol=2) # create matrix 
B = matrix(c(3,7), nrow=2, ncol=1) # create matrix
a = matrix(c(4,2), nrow=2, ncol=1) # create vector - matrix with one column
b = matrix(c(-1,5), nrow=2, ncol=1) # create vector - matrix with one column

# Matrix multiplication (two kinds, be careful!)
wrongResult = A * B # A*B is element-by-element multiplication - wrong!!!
rightResult = A %*% B # A%*%B is matrix multiplication - right!!!

t(A) # Matrix transposition (ie. rows become columns,  columns become rows)

# Vector addition
c = a + b # adds two vectors using built-in rules

# Scalar (vector) multiplication
c = 0.5 * b # adds two vectors using built-in rules