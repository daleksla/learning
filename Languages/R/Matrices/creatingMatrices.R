# Enter a matrix (three methods)
A = matrix(c(2,3,5,7), nrow=2, ncol=2) # top to bottom (column), left to right (row)
B = rbind(c(1,2),c(8,9)) # bind rows together
C = cbind(c(1,2),c(8,9)) # bind columns together

# Diagonal matrices (numbers only on the main diagonal
# from top-left to bottom-right, everything else zero)
diag(c(3,7))
I = diag(c(1,1)) # Identity matrix (ones on main diagonal, else zero)

# To create vectors (single column matrices)
a = matrix(c(4,2), nrow=2, ncol=1)
b = matrix(c(-1,5), nrow=2, ncol=1)