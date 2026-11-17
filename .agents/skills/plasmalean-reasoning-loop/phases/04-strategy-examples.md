# Examples of Good Strategy Generation

## Forward Reasoning Example
*   *Hypothesis:* $G$ is a finite group of order $p^n$.
*   *Deduction:* By Sylow's Theorems, $G$ has a non-trivial center $Z(G)$.

## Proof Sketch Example
**Plan A: Proof by Contradiction**
*   **Step 1 (easy):** Assume for contradiction that $\sqrt{2} = a/b$ where $a,b$ are coprime.
*   **Step 2 (standard):** Deduce that $a^2 = 2b^2$, hence $a^2$ is even.
*   **Step 3 (hard):** Lemma: Prove that if $a^2$ is even, then $a$ is even. *(Note: Requires recursive loop).*
*   **Step 4 (standard):** Substitute $a=2k$ to show $b^2$ is even, implying $b$ is even, contradicting coprimality.
