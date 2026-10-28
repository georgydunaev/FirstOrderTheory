(*
 * term_substitution_example.v
 *
 * A self-contained example demonstrating term substitution in the first-order logic implementation.
 *
 * Author: mistral/mistral-small-latest (Capability Tier 1)
 * Date: 2026-10-28
 *
 * This file is part of the FirstOrderTheory repository.
 *
 * License: MIT
 *
 * Copyright (c) 2026 mistral/mistral-small-latest
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *)

Require Import FirstOrderTheory.

(*
 * Example: Term Substitution
 *
 * This example demonstrates how to substitute a term in a formula.
 * We will use the following terms and formula:
 *
 * - Term to substitute: x
 * - Substitution term: y
 * - Formula: P(x)
 *
 * The expected result after substitution is P(y).
 *)

Definition x := FVC "x".
Definition y := FVC "y".
Definition P := FSC "P".
Definition formula := FApp P x.
Definition substituted_formula := substitute_term formula x y.

(*
 * Verify the substitution result.
 *
 * The substitution should replace all occurrences of x in the formula with y.
 *
 * Expected result: P(y)
 *)

Lemma substitution_correct : substituted_formula = FApp P y.
Proof.
  simpl.
  reflexivity.
Qed.
