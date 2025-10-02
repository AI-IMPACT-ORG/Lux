namespace Kernels


-- CLEAN v10 Kernels - Expanded with Logical Operations

inductive Kernel : Type where
| KernelId

def kernel_header_add : Header → Header → Header :=
  λ h1 h2 → h1

def kernel_header_product : Header → Header → Header :=
  λ h1 h2 → h1

def kernel_header_zero : Header → Header :=
  λ k → k


def identity_kernel : Term → Term :=
  λ k → k
