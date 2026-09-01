/-
# Lean Kernel Soundness Tools

This library provides tools for reasoning about Lean kernel soundness:
- A specification of the Lean export file format
- A kernel abstraction that wraps kernel execution
- Soundness and consistency properties
- Dummy kernels for testing
- A final composed theorem: sound kernel → consistent
-/

import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.Typing.Expr
import Lean4LeanModel.StandardAxioms
