import numpy as np

def doolittle_lup_decomposition(A):
    n = A.shape[0]
    L = np.eye(n)
    U = np.zeros((n, n))
    P = np.eye(n)

    for k in range(n):
        max_row = np.argmax(np.abs(A[k:, k])) + k
        if max_row != k:
            P[[k, max_row]] = P[[max_row, k]]
            A[[k, max_row]] = A[[max_row, k]]

        for i in range(k + 1, n):
            L[i, k] = A[i, k] / A[k, k]
            A[i, k:] -= L[i, k] * A[k, k:]

        U[k, k:] = A[k, k:]

    return P, L, U

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
print("\nReconstructing A from PLU:")
print(np.dot(P, np.dot(L, U)))
