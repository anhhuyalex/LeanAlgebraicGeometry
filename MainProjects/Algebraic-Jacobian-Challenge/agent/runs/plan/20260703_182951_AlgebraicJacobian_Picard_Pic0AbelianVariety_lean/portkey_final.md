### 1. Natural Language Explanation of the Goal

The Lean theorem `tangentSpaceIso` formalizes the **Zariski tangent-space isomorphism at the identity** of the Picard scheme $\text{Pic}^0_{C/k}$ of a curve $C/k$. 

Specifically, let $C/k$ be a smooth, proper, geometrically integral curve of relative dimension 1 over a field $k$, and let $\text{Pic}^0_{C/k}$ denote the identity component of its Picard scheme. The theorem asserts that there exists (witnessed by `Nonempty` and the $\Sigma'$-type) a $k$-rational identity-section point:
$$e \colon \operatorname{Spec} k \longrightarrow (\operatorname{Pic}^0_{C/k})_{\text{red}}$$
such that the algebraic **cotangent space** at $e$, defined as the quotient $\mathfrak{m}_e / \mathfrak{m}_e^2$ of the maximal ideal of the local ring (stalk) $\mathcal{O}_{\operatorname{Pic}^0_{C/k}, e}$, is canonically isomorphic as an additive group (`≃+`) to the first sheaf cohomology group $H^1(C, \mathcal{O}_C)$ (represented by the project's $H^1$-cohomology module `Scheme.HModule k (Scheme.toModuleKSheaf C) 1`).

---

### 2. Equation of the Goal in KaTeX

The canonical isomorphism of $k$-vector spaces (or their underlying additive groups) is formulated as:

$$\tu T_0 \Pic^0_{C/k} \;\cong\; H^1(C, \mathcal{O}_C)$$

And for the cotangent space:

$$\left( \mathfrak{m}_0 / \mathfrak{m}_0^2 \right) \;\cong_{\text{add}}\; H^1(C, \mathcal{O}_C)$$

---

### 3. Rigorous Mathematical Proof (Putnam Style)

#### **Theorem**
Let $C/k$ be a smooth, proper, geometrically integral curve of genus $g$ over a field $k$, and let $\operatorname{Pic}^0_{C/k}$ be the identity component of the Picard scheme of $C/k$. There is a canonical isomorphism of $k$-vector spaces:
$$ T_0 \operatorname{Pic}^0_{C/k} \cong H^1(C, \mathcal{O}_C) $$

#### **Proof**
**Step 1: Zariski Tangent Space via Dual Numbers**
Let $k[\varepsilon] = k[t]/(t^2)$ be the ring of dual numbers over $k$. For any scheme $X$ over $k$ and a $k$-rational point $x \colon \operatorname{Spec} k \to X$, the Zariski tangent space $T_x X$ is canonically isomorphic to the fiber of the morphism:
$$ X(k[\varepsilon]) \longrightarrow X(k) $$
above $x$. 
Let $X = \operatorname{Pic}_{C/k}$ be the Picard scheme of $C/k$. Since the identity component $\operatorname{Pic}^0_{C/k}$ is an open subscheme of $\operatorname{Pic}_{C/k}$ containing the identity $0 \in \operatorname{Pic}_{C/k}(k)$, their local rings at $0$ are isomorphic. Hence:
$$ T_0 \operatorname{Pic}^0_{C/k} \cong T_0 \operatorname{Pic}_{C/k} $$
The identity $0 \in \operatorname{Pic}_{C/k}(k)$ corresponds to the trivial line bundle on $C$. Thus, $T_0 \operatorname{Pic}_{C/k}$ is isomorphic to the kernel of the reduction map:
$$ \operatorname{Pic}_{C/k}(k[\varepsilon]) \longrightarrow \operatorname{Pic}_{C/k}(k) $$

**Step 2: Representation of the Picard Functor**
Since $C/k$ is proper and geometrically integral, the Picard functor is represented by the Picard scheme $\operatorname{Pic}_{C/k}$. For any $k$-algebra $R$, we have:
$$ \operatorname{Pic}_{C/k}(R) \cong \operatorname{Pic}(C_R) / p^* \operatorname{Pic}(R) $$
where $C_R = C \times_{\operatorname{Spec} k} \operatorname{Spec} R$.
For the local ring $R = k[\varepsilon]$, any line bundle on $\operatorname{Spec} k[\varepsilon]$ is trivial, so $\operatorname{Pic}(k[\varepsilon]) = 0$. Hence:
$$ \operatorname{Pic}_{C/k}(k[\varepsilon]) \cong \operatorname{Pic}(C_{k[\varepsilon]}) $$
and the reduction map corresponds to:
$$ \operatorname{Pic}(C_{k[\varepsilon]}) \longrightarrow \operatorname{Pic}(C) $$
whose kernel is the group of line bundles on $C_{k[\varepsilon]}$ that restrict to the trivial line bundle on $C$.

**Step 3: The Split Truncated Exponential Sequence**
Topologically, the space $C_{k[\varepsilon]}$ is identical to $C$. Its structure sheaf is given by $\mathcal{O}_{C_{k[\varepsilon]}} \cong \mathcal{O}_C \otimes_k k[\varepsilon] \cong \mathcal{O}_C \oplus \varepsilon \mathcal{O}_C$.
We define a sequence of sheaves of abelian groups on the topological space of $C$:
$$ 0 \longrightarrow \mathcal{O}_C \xrightarrow{\quad\alpha\quad} \mathcal{O}_{C_{k[\varepsilon]}}^\times \xrightarrow{\quad\beta\quad} \mathcal{O}_C^\times \longrightarrow 1 $$
where:
* $\alpha(x) = 1 + x\varepsilon$
* $\beta(u + v\varepsilon) = u$ (since $u + v\varepsilon$ is a unit if and only if $u \in \mathcal{O}_C^\times$).

We check that $\alpha$ is a group homomorphism from the additive group of $\mathcal{O}_C$ to the multiplicative group of units $\mathcal{O}_{C_{k[\varepsilon]}}^\times$:
$$ \alpha(x)\alpha(y) = (1 + x\varepsilon)(1 + y\varepsilon) = 1 + (x+y)\varepsilon + xy\varepsilon^2 = 1 + (x+y)\varepsilon = \alpha(x+y) $$
since $\varepsilon^2 = 0$. $\beta$ is clearly a surjective homomorphism of multiplicative groups, and its kernel is precisely the image of $\alpha$.
Furthermore, the inclusion $\gamma \colon \mathcal{O}_C^\times \to \mathcal{O}_{C_{k[\varepsilon]}}^\times$ provides a splitting of $\beta$ (i.e., $\beta \circ \gamma = \text{id}$).
Thus, we have a split exact sequence of sheaves of abelian groups on $C$.

**Step 4: Sheaf Cohomology Comparison**
Taking the long exact sequence in sheaf cohomology associated to this split short exact sequence of sheaves, we obtain a split exact sequence of abelian groups:
$$ 0 \longrightarrow H^1(C, \mathcal{O}_C) \longrightarrow H^1(C_{k[\varepsilon]}, \mathcal{O}_{C_{k[\varepsilon]}}^\times) \xrightarrow{\quad\beta_*\quad} H^1(C, \mathcal{O}_C^\times) \longrightarrow 0 $$
Using the canonical identification $H^1(X, \mathcal{O}_X^\times) \cong \operatorname{Pic}(X)$, this exact sequence yields:
$$ 0 \longrightarrow H^1(C, \mathcal{O}_C) \longrightarrow \operatorname{Pic}(C_{k[\varepsilon]}) \xrightarrow{\quad\text{red}\quad} \operatorname{Pic}(C) \longrightarrow 0 $$
Thus, there is a canonical isomorphism of abelian groups:
$$ \ker(\operatorname{Pic}(C_{k[\varepsilon]}) \to \operatorname{Pic}(C)) \cong H^1(C, \mathcal{O}_C) $$

**Step 5: $k$-Linearity and Conclusion**
The isomorphism is canonical and respects the $k$-vector space structure (where the action of $a \in k$ on the dual-number tangent space via the endomorphism $\varepsilon \mapsto a\varepsilon$ of $k[\varepsilon]$ corresponds to scalar multiplication by $a$ on $H^1(C, \mathcal{O}_C)$). Dualizing this relation yields the cotangent-space isomorphism:
$$ (\mathfrak{m}_0 / \mathfrak{m}_0^2) \cong H^1(C, \mathcal{O}_C) $$
which completes the proof.

$\blacksquare$

---

### 4. Blueprint & Implementation Plan

The Lean proof of `tangentSpaceIso` is completed modulo `tangentSpaceEquiv`. To fully close the remaining typed sorry in `tangentSpaceEquiv`, the following milestones must be achieved:

1. **Dual Numbers and Tangent Space API:**
   * Formulate the ring of dual numbers $k[\varepsilon]$ in Mathlib and represent the functorial definition of the tangent space of a scheme $X$ over $k$ at a rational point.
   * Provide the equivalence between the dual-number definition $\operatorname{Hom}_{k\text{-alg}}(\mathcal{O}_{X,x}, k[\varepsilon])$ and the algebraic cotangent space $(\mathfrak{m}_x / \mathfrak{m}_x^2)^\vee$.

2. **The Picard Functor over Dual Numbers:**
   * Formalize the split short exact sequence of sheaves of abelian groups:
     $$ 0 \to \mathcal{O}_C \to \mathcal{O}_{C_{k[\varepsilon]}}^\times \to \mathcal{O}_C^\times \to 1 $$
   * Establish the long exact sequence in sheaf cohomology for this split sequence and extract the split exact sequence of $H^1$ groups.

3. **Isomorphism Assembly:**
   * Bridge the $H^1(C_{k[\varepsilon]}, \mathcal{O}_{C_{k[\varepsilon]}}^\times)$ class representation to $\operatorname{Pic}(C_{k[\varepsilon]})$ and show that the kernel of the reduction map is isomorphic to $H^1(C, \mathcal{O}_C)$.
   * Use the `identitySection` witness to close the typed sorry in `tangentSpaceEquiv`.