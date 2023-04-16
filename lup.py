import numpy as np

def doolittle_lup_decomposition(A):
    n = A.shape[0]
    L = np.eye(n)
    U = np.zeros((n, n))
    P = np.eye(n)

    for k in range(n):
        # Select the subarray of the current column, below the diagonal
        current_column = A[k:, k]

        # Find the index of the maximum absolute value in the current_column
        max_index = np.argmax(np.abs(current_column))

        # Add k to the max_index to get the actual row index in the original matrix A
        max_row = max_index + k

        # Swap rows in both P and A matrices to make sure the largest value is on the diagonal
        P[[k, max_row]] = P[[max_row, k]]
        A[[k, max_row]] = A[[max_row, k]]

        # Perform Gaussian elimination to create zeros below the diagonal in the current column
        for i in range(k + 1, n):
            # Compute the multiplier for the Gaussian elimination
            L[i, k] = A[i, k] / A[k, k]
            # Update the rows below the current row in A, effectively performing Gaussian elimination
            A[i, k:] -= L[i, k] * A[k, k:]

        # Assign the upper triangular part of A to U
        U[k, k:] = A[k, k:]

    return P, L, U


def invert_matrix(A):
    n = A.shape[0]
    inv = np.eye(n)
    P, L, U = doolittle_lup_decomposition(A)

    for k in range(n):
        b = P @ inv[:, k]
        x = forward_substitution(L, b)
        y = back_substitution(U, x)
        inv[:, k] = y

    return inv

def forward_substitution(L, b):
    n = L.shape[0]
    x = np.zeros(n)
    print("forward subst: L")
    print(L)
    print(f"b: {b}")
    for i in range(n):
        x[i] = b[i] - np.sum(L[i, :i] * x[:i])
        print(x[i])
    return x

def back_substitution(U, y):
    n = U.shape[0]
    x = np.zeros(n)
    for i in range(n - 1, -1, -1):
        x[i] = (y[i] - np.sum(U[i, i + 1:] * x[i + 1:])) / U[i, i]
    return x

# Test the implementation
A = np.array([[4, 3, -1],
              [5, 3, 2],
              [2, 1, 3]], dtype=float)
print("Original Matrix A:")
print(A)

P, L, U = doolittle_lup_decomposition(A)

print("\nPermutation Matrix P:")
print(P)
print("\nLower Triangular Matrix L:")
print(L)
print("\nUpper Triangular Matrix U:")
print(U)


b = np.array([1, 2, 3], dtype=float)

x = forward_substitution(L, b)
print(f"Forward substitution on L with {b}")
print(x)  # Expected output: [1.  1.2 3. ]

print(f"Back substitution on U with {b}")
x = back_substitution(U, b)
print(x)  # Expected output: [-8.55       13.08333333  2.25      ]

print("\nIntermediate: LU:")
print(np.dot(L, U))
print("\nReconstructing A from PLU:")
print(np.dot(P, np.dot(L, U)))

print("\nMatrix A inverse:")
A_inv = invert_matrix(A)
print(A_inv)

print("\nA * A_inv:")
print(np.dot(A, A_inv))