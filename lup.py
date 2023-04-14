import numpy as np

def lup_decomposition(A):
    n = A.shape[0]
    L = np.zeros((n, n))
    U = np.zeros((n, n))
    P = np.eye(n)

    for k in range(n):
        pivot = np.argmax(np.abs(A[k:, k])) + k
        A[[k, pivot]] = A[[pivot, k]]
        P[[k, pivot]] = P[[pivot, k]]

        L[k, k] = 1
        for i in range(k + 1, n):
            L[i, k] = A[i, k] / A[k, k]
            A[i, k:] -= L[i, k] * A[k, k:]
        U[k, k:] = A[k, k:]

    return L, U, P

# Example usage
A = np.array([[2, 0, 2, 0.6],
              [3, 3, 4, -2],
              [5, 5, 4, 2],
              [-1, -2, 3.4, -1]])

L, U, P = lup_decomposition(A)

print("L:")
print(L)
print("U:")
print(U)
print("P:")
print(P)

# Verify the decomposition
print("PA:")
print(np.dot(P, A))
print("LU:")
print(np.dot(L, U))
