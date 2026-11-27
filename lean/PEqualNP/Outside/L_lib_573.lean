import Mathlib
import PEqualNP.Defs

-- A circuit of two-input AND/OR gates with free MOD 2 gates (at most two inputs) and free NOT gates: every
-- flat p + U splits into at most 2^cost flats, each of codimension at most cost in U, on each of which every
-- wire is an affine form; cost is the number of AND and OR gates.
--
-- Proof: induction over the gate list, last gate first removed. With no gates the one part is p + U and
-- wire i is the coordinate x_i. A MOD 2 gate or a NOT gate is affine in the wires it reads, so every part is
-- kept. For an AND or OR gate reading wires i and j, a part on which wire i takes both values is cut by the
-- kernel of the weight of wire i into two parallel flats (one dimension lost at most); on a part where wire i
-- is constant the gate is a constant or a copy of wire j. The parts are kept as a finite set of pairs
-- (base point, direction) and numbered only at the end.

namespace PEqualNP.Outside.L_lib_573

open PEqualNP.CircuitLowerBounds

abbrev K := ZMod 2
abbrev X (n : ℕ) := Fin n → K

/-- The wire list after running a gate list on a wire list: the fold inside `Circuit.wires`. -/
def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    W (gs ++ [g]) w = W gs w ++ [g.op.eval (g.inputs.map fun i => (W gs w).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (w : List Bool) : (W gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem new_wire (gs : List Gate) (g : Gate) (w : List Bool) :
    (W (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun t => (W gs w).getD t false) := by
  rw [W_snoc, getD_snoc]; simp [W_len]

theorem old_wire (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i ≠ w.length + gs.length) :
    (W (gs ++ [g]) w).getD i false = (W gs w).getD i false := by
  rw [W_snoc, getD_snoc]; simp [W_len, hi]

/-- The input word of a point. -/
def inp {n : ℕ} (x : X n) : List Bool := List.ofFn (fun i : Fin n => decide (x i = 1))

theorem inp_len {n : ℕ} (x : X n) : (inp x).length = n := by simp [inp]

/-- Every wire of the gate list is an affine form on the flat `b + D`. -/
def Aff (n : ℕ) (gs : List Gate) (b : X n) (D : Submodule K (X n)) : Prop :=
  ∀ wire : ℕ, ∃ (weight : X n) (offset : K), ∀ point : X n, point - b ∈ D →
    (W gs (inp point)).getD wire false = decide (dotProduct weight point + offset = 1)

theorem aff_mono {n : ℕ} (gs : List Gate) (b b' : X n) (D D' : Submodule K (X n))
    (h : Aff n gs b D) (hb : b' - b ∈ D) (hD : D' ≤ D) : Aff n gs b' D' := by
  intro wire
  obtain ⟨wt, off, hwo⟩ := h wire
  refine ⟨wt, off, fun point hp => hwo point ?_⟩
  have : point - b = (point - b') + (b' - b) := by abel
  rw [this]; exact D.add_mem (hD hp) hb

theorem aff_snoc {n : ℕ} (gs : List Gate) (g : Gate) (b : X n) (D : Submodule K (X n))
    (h : Aff n gs b D)
    (hnew : ∃ (weight : X n) (offset : K), ∀ point : X n, point - b ∈ D →
      g.op.eval (g.inputs.map fun t => (W gs (inp point)).getD t false) =
        decide (dotProduct weight point + offset = 1)) :
    Aff n (gs ++ [g]) b D := by
  intro wire
  by_cases hw : wire = n + gs.length
  · obtain ⟨wt, off, hwo⟩ := hnew
    refine ⟨wt, off, fun point hp => ?_⟩
    have e := new_wire gs g (inp point)
    rw [inp_len] at e
    rw [hw, e, hwo point hp]
  · obtain ⟨wt, off, hwo⟩ := h wire
    refine ⟨wt, off, fun point hp => ?_⟩
    rw [old_wire gs g (inp point) wire (by rw [inp_len]; exact hw)]
    exact hwo point hp

theorem aff_nil (n : ℕ) (b : X n) (D : Submodule K (X n)) : Aff n [] b D := by
  intro wire
  by_cases hw : wire < n
  · refine ⟨Pi.single ⟨wire, hw⟩ 1, 0, fun point _ => ?_⟩
    have h1 : (W [] (inp point)).getD wire false = decide (point ⟨wire, hw⟩ = 1) := by
      show (inp point).getD wire false = _
      rw [List.getD_eq_getElem _ _ (by rw [inp_len]; exact hw)]
      simp [inp]
    rw [h1]; simp [single_dotProduct]
  · refine ⟨0, 0, fun point _ => ?_⟩
    have h1 : (W [] (inp point)).getD wire false = false := by
      show (inp point).getD wire false = _
      exact List.getD_eq_default _ _ (by rw [inp_len]; omega)
    rw [h1]; simp

theorem z_not (A : K) : (!decide (A = 1)) = decide (A + 1 = 1) := by revert A; decide
theorem z_one (A : K) :
    decide (List.count true [decide (A = 1)] % 2 = 0) = decide (A + 1 = 1) := by revert A; decide
theorem z_two (A B : K) :
    decide (List.count true [decide (A = 1), decide (B = 1)] % 2 = 0) = decide (A + B + 1 = 1) := by
  revert A B; decide
theorem z_eq (a b : K) (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by revert a b; decide

/-- A MOD 2 gate with at most two inputs, or a NOT gate with one, is affine where the wires it reads are. -/
theorem new_free {n : ℕ} (gs : List Gate) (g : Gate) (b : X n) (D : Submodule K (X n))
    (h : Aff n gs b D)
    (hfree : (g.op = GateOp.mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∃ (weight : X n) (offset : K), ∀ point : X n, point - b ∈ D →
      g.op.eval (g.inputs.map fun t => (W gs (inp point)).getD t false) =
        decide (dotProduct weight point + offset = 1) := by
  rcases hfree with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
  · rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · refine ⟨0, 1, fun point _ => ?_⟩
      rw [hop]; simp [GateOp.eval]
    · obtain ⟨wa, oa, ha⟩ := h i
      refine ⟨wa, oa + 1, fun point hp => ?_⟩
      rw [hop]
      show decide (List.count true [(W gs (inp point)).getD i false] % 2 = 0) = _
      rw [ha point hp, z_one, add_assoc]
    · obtain ⟨wa, oa, ha⟩ := h i
      obtain ⟨wb, ob, hb⟩ := h j
      refine ⟨wa + wb, oa + ob + 1, fun point hp => ?_⟩
      have e : dotProduct (wa + wb) point + (oa + ob + 1) =
          (dotProduct wa point + oa) + (dotProduct wb point + ob) + 1 := by
        rw [add_dotProduct]; ring
      rw [hop, e]
      show decide (List.count true [(W gs (inp point)).getD i false,
        (W gs (inp point)).getD j false] % 2 = 0) = _
      rw [ha point hp, hb point hp, z_two]
    · exfalso
      rw [hin] at hlen
      have : 3 ≤ (i :: j :: k :: l).length := by simp
      omega
  · rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, l⟩⟩
    · exfalso; rw [hin] at hlen; simp at hlen
    · obtain ⟨wa, oa, ha⟩ := h i
      refine ⟨wa, oa + 1, fun point hp => ?_⟩
      rw [hop]
      show (!((W gs (inp point)).getD i false)) = _
      rw [ha point hp, z_not, add_assoc]
    · exfalso
      rw [hin] at hlen
      have : 2 ≤ (i :: j :: l).length := by simp
      omega

/-- An AND or OR gate reading wires `i` and `j` is affine on a flat where wire `i` is constant. -/
theorem new_paid {n : ℕ} (gs : List Gate) (g : Gate) (b : X n) (D : Submodule K (X n))
    (h : Aff n gs b D) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (i j : ℕ)
    (hin : g.inputs = [i, j]) (c : Bool)
    (hc : ∀ point : X n, point - b ∈ D → (W gs (inp point)).getD i false = c) :
    ∃ (weight : X n) (offset : K), ∀ point : X n, point - b ∈ D →
      g.op.eval (g.inputs.map fun t => (W gs (inp point)).getD t false) =
        decide (dotProduct weight point + offset = 1) := by
  obtain ⟨wb, ob, hb⟩ := h j
  rcases hop with hop | hop <;> cases c
  · refine ⟨0, 0, fun point hp => ?_⟩
    rw [hop, hin]
    show ((W gs (inp point)).getD i false && ((W gs (inp point)).getD j false && true)) = _
    rw [hc point hp]; simp
  · refine ⟨wb, ob, fun point hp => ?_⟩
    rw [hop, hin]
    show ((W gs (inp point)).getD i false && ((W gs (inp point)).getD j false && true)) = _
    rw [hc point hp, hb point hp]; simp
  · refine ⟨wb, ob, fun point hp => ?_⟩
    rw [hop, hin]
    show ((W gs (inp point)).getD i false || ((W gs (inp point)).getD j false || false)) = _
    rw [hc point hp, hb point hp]; simp
  · refine ⟨0, 1, fun point hp => ?_⟩
    rw [hop, hin]
    show ((W gs (inp point)).getD i false || ((W gs (inp point)).getD j false || false)) = _
    rw [hc point hp]; simp

/-- The weight of a wire as a linear form. -/
def phi {n : ℕ} (w : X n) : X n →ₗ[K] K where
  toFun x := dotProduct w x
  map_add' := dotProduct_add w
  map_smul' c x := by simp [dotProduct_smul]

theorem finrank_cut {n : ℕ} (D : Submodule K (X n)) (w : X n) :
    Module.finrank K D ≤ Module.finrank K ↥(D ⊓ LinearMap.ker (phi w)) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq D (LinearMap.ker (phi w))
  have h2 := LinearMap.finrank_range_add_finrank_ker (phi w)
  have h3 : Module.finrank K ↥(LinearMap.range (phi w)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (phi w))
    simpa using this
  have h4 := Submodule.finrank_le (D ⊔ LinearMap.ker (phi w))
  omega

/-- A part that is kept whole. -/
theorem keep {n : ℕ} (gs : List Gate) (g : Gate) (b : X n) (D : Submodule K (X n)) (k : ℕ)
    (h : Aff n (gs ++ [g]) b D) :
    ∃ S : Finset (X n × Submodule K (X n)), S.card ≤ 2 ^ k ∧
      (∀ Q ∈ S, Q.1 - b ∈ D ∧ Q.2 ≤ D ∧ Module.finrank K D ≤ Module.finrank K Q.2 + k ∧
        Aff n (gs ++ [g]) Q.1 Q.2) ∧
      (∀ x : X n, x - b ∈ D → ∃! Q, Q ∈ S ∧ x - Q.1 ∈ Q.2) := by
  refine ⟨{(b, D)}, ?_, ?_, ?_⟩
  · rw [Finset.card_singleton]; exact Nat.one_le_two_pow
  · intro Q hQ
    rw [Finset.mem_singleton] at hQ; subst hQ
    exact ⟨by simp, le_refl _, Nat.le_add_right _ _, h⟩
  · intro x hx
    exact ⟨(b, D), ⟨Finset.mem_singleton_self _, hx⟩, fun Q hQ => Finset.mem_singleton.1 hQ.1⟩

/-- An AND or OR gate cuts a part into at most two. -/
theorem split_paid {n : ℕ} (gs : List Gate) (g : Gate) (b : X n) (D : Submodule K (X n))
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2) (h : Aff n gs b D) :
    ∃ S : Finset (X n × Submodule K (X n)), S.card ≤ 2 ^ 1 ∧
      (∀ Q ∈ S, Q.1 - b ∈ D ∧ Q.2 ≤ D ∧ Module.finrank K D ≤ Module.finrank K Q.2 + 1 ∧
        Aff n (gs ++ [g]) Q.1 Q.2) ∧
      (∀ x : X n, x - b ∈ D → ∃! Q, Q ∈ S ∧ x - Q.1 ∈ Q.2) := by
  classical
  obtain ⟨i, j, hin⟩ := List.length_eq_two.1 hlen
  obtain ⟨wa, oa, ha⟩ := h i
  by_cases h1 : ∃ x1 : X n, x1 - b ∈ D ∧ dotProduct wa x1 + oa = 1
  · by_cases h0 : ∃ x0 : X n, x0 - b ∈ D ∧ dotProduct wa x0 + oa ≠ 1
    · obtain ⟨x1, hx1, e1⟩ := h1
      obtain ⟨x0, hx0, e0⟩ := h0
      have key : ∀ xc point : X n, point - xc ∈ D ⊓ LinearMap.ker (phi wa) →
          dotProduct wa point = dotProduct wa xc := by
        intro xc point hp
        have hk : dotProduct wa (point - xc) = 0 := LinearMap.mem_ker.1 hp.2
        rw [dotProduct_sub] at hk
        exact sub_eq_zero.1 hk
      have inflat : ∀ xc : X n, xc - b ∈ D → ∀ point : X n,
          point - xc ∈ D ⊓ LinearMap.ker (phi wa) → point - b ∈ D := by
        intro xc hxc point hp
        have : point - b = (point - xc) + (xc - b) := by abel
        rw [this]; exact D.add_mem hp.1 hxc
      have child : ∀ (xc : X n) (c : Bool), xc - b ∈ D →
          decide (dotProduct wa xc + oa = 1) = c →
          Aff n (gs ++ [g]) xc (D ⊓ LinearMap.ker (phi wa)) := by
        intro xc c hxc hc
        have hA := aff_mono gs b xc D (D ⊓ LinearMap.ker (phi wa)) h hxc inf_le_left
        refine aff_snoc gs g xc _ hA (new_paid gs g xc _ hA hop i j hin c ?_)
        intro point hp
        rw [ha point (inflat xc hxc point hp), key xc point hp, hc]
      refine ⟨{(x0, D ⊓ LinearMap.ker (phi wa)), (x1, D ⊓ LinearMap.ker (phi wa))},
        Finset.card_le_two, ?_, ?_⟩
      · intro Q hQ
        rcases Finset.mem_insert.1 hQ with rfl | hQ
        · exact ⟨hx0, inf_le_left, finrank_cut D wa, child x0 false hx0 (by simpa using e0)⟩
        · rw [Finset.mem_singleton] at hQ; subst hQ
          exact ⟨hx1, inf_le_left, finrank_cut D wa, child x1 true hx1 (by simpa using e1)⟩
      · intro x hx
        have mem : ∀ xc : X n, xc - b ∈ D → dotProduct wa x = dotProduct wa xc →
            x - xc ∈ D ⊓ LinearMap.ker (phi wa) := by
          intro xc hxc he
          refine ⟨?_, LinearMap.mem_ker.2 ?_⟩
          · have : x - xc = (x - b) - (xc - b) := by abel
            rw [this]; exact D.sub_mem hx hxc
          · show dotProduct wa (x - xc) = 0
            rw [dotProduct_sub, he, sub_self]
        by_cases hv : dotProduct wa x + oa = 1
        · refine ⟨(x1, D ⊓ LinearMap.ker (phi wa)),
            ⟨by simp, mem x1 hx1 (add_right_cancel (hv.trans e1.symm))⟩, ?_⟩
          rintro Q ⟨hQ, hxQ⟩
          rcases Finset.mem_insert.1 hQ with rfl | hQ
          · exact absurd (by rw [← key x0 x hxQ]; exact hv) e0
          · exact Finset.mem_singleton.1 hQ
        · refine ⟨(x0, D ⊓ LinearMap.ker (phi wa)),
            ⟨by simp, mem x0 hx0 (add_right_cancel (z_eq _ _ hv e0))⟩, ?_⟩
          rintro Q ⟨hQ, hxQ⟩
          rcases Finset.mem_insert.1 hQ with rfl | hQ
          · rfl
          · rw [Finset.mem_singleton] at hQ; subst hQ
            exact absurd (by rw [key x1 x hxQ]; exact e1) hv
    · have hall : ∀ x0 : X n, x0 - b ∈ D → dotProduct wa x0 + oa = 1 := by
        intro x0 hx0
        by_contra hne
        exact h0 ⟨x0, hx0, hne⟩
      exact keep gs g b D 1 (aff_snoc gs g b D h (new_paid gs g b D h hop i j hin true
        (fun point hp => by rw [ha point hp]; simpa using hall point hp)))
  · have hall : ∀ x1 : X n, x1 - b ∈ D → dotProduct wa x1 + oa ≠ 1 :=
      fun x1 hx1 hne => h1 ⟨x1, hx1, hne⟩
    exact keep gs g b D 1 (aff_snoc gs g b D h (new_paid gs g b D h hop i j hin false
      (fun point hp => by rw [ha point hp]; simpa using hall point hp)))

/-- The number of AND and OR gates, written as in the statement. -/
noncomputable def cost (gs : List Gate) : ℕ :=
  gs.countP (fun g => @decide (g.op = GateOp.and ∨ g.op = GateOp.or) (Classical.propDecidable _))

theorem cost_snoc_paid (gs : List Gate) (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) :
    cost (gs ++ [g]) = cost gs + 1 := by
  unfold cost
  rw [List.countP_append]
  simp [h]

theorem cost_snoc_free (gs : List Gate) (g : Gate) (h : ¬ (g.op = GateOp.and ∨ g.op = GateOp.or)) :
    cost (gs ++ [g]) = cost gs := by
  unfold cost
  rw [List.countP_append]
  simp [h]

/-- One gate more: every part is replaced by the parts it is cut into. -/
theorem glue {n : ℕ} (U : Submodule K (X n)) (p : X n) (gs : List Gate) (g : Gate) (c k : ℕ)
    (parts : Finset (X n × Submodule K (X n)))
    (hcard : parts.card ≤ 2 ^ c)
    (hP : ∀ P ∈ parts, P.1 - p ∈ U ∧ P.2 ≤ U ∧ Module.finrank K U ≤ Module.finrank K P.2 + c)
    (hcov : ∀ x : X n, x - p ∈ U → ∃! P, P ∈ parts ∧ x - P.1 ∈ P.2)
    (hstep : ∀ P ∈ parts, ∃ S : Finset (X n × Submodule K (X n)), S.card ≤ 2 ^ k ∧
      (∀ Q ∈ S, Q.1 - P.1 ∈ P.2 ∧ Q.2 ≤ P.2 ∧
        Module.finrank K P.2 ≤ Module.finrank K Q.2 + k ∧ Aff n (gs ++ [g]) Q.1 Q.2) ∧
      (∀ x : X n, x - P.1 ∈ P.2 → ∃! Q, Q ∈ S ∧ x - Q.1 ∈ Q.2)) :
    ∃ parts' : Finset (X n × Submodule K (X n)), parts'.card ≤ 2 ^ (c + k) ∧
      (∀ P ∈ parts', P.1 - p ∈ U ∧ P.2 ≤ U ∧
        Module.finrank K U ≤ Module.finrank K P.2 + (c + k)) ∧
      (∀ x : X n, x - p ∈ U → ∃! P, P ∈ parts' ∧ x - P.1 ∈ P.2) ∧
      (∀ P ∈ parts', Aff n (gs ++ [g]) P.1 P.2) := by
  classical
  choose S hS1 hS2 hS3 using hstep
  refine ⟨parts.attach.biUnion (fun P => S P.1 P.2), ?_, ?_, ?_, ?_⟩
  · calc (parts.attach.biUnion fun P => S P.1 P.2).card
        ≤ ∑ P ∈ parts.attach, (S P.1 P.2).card := Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ parts.attach, 2 ^ k := Finset.sum_le_sum (fun P _ => hS1 P.1 P.2)
      _ = parts.card * 2 ^ k := by simp
      _ ≤ 2 ^ c * 2 ^ k := Nat.mul_le_mul_right _ hcard
      _ = 2 ^ (c + k) := (pow_add 2 c k).symm
  · intro Q hQ
    obtain ⟨⟨P, hPm⟩, -, hQS⟩ := Finset.mem_biUnion.1 hQ
    obtain ⟨h1, h2, h3, -⟩ := hS2 P hPm Q hQS
    obtain ⟨g1, g2, g3⟩ := hP P hPm
    refine ⟨?_, h2.trans g2, by omega⟩
    have : Q.1 - p = (Q.1 - P.1) + (P.1 - p) := by abel
    rw [this]; exact U.add_mem (g2 h1) g1
  · intro x hx
    obtain ⟨P, ⟨hPm, hxP⟩, hPu⟩ := hcov x hx
    obtain ⟨Q, ⟨hQS, hxQ⟩, hQu⟩ := hS3 P hPm x hxP
    refine ⟨Q, ⟨Finset.mem_biUnion.2 ⟨⟨P, hPm⟩, Finset.mem_attach _ _, hQS⟩, hxQ⟩, ?_⟩
    rintro Q' ⟨hQ', hxQ'⟩
    obtain ⟨⟨P', hP'm⟩, -, hQ'S⟩ := Finset.mem_biUnion.1 hQ'
    obtain ⟨h1, h2, -, -⟩ := hS2 P' hP'm Q' hQ'S
    have hxP' : x - P'.1 ∈ P'.2 := by
      have : x - P'.1 = (x - Q'.1) + (Q'.1 - P'.1) := by abel
      rw [this]; exact P'.2.add_mem (h2 hxQ') h1
    have hPP : P' = P := hPu P' ⟨hP'm, hxP'⟩
    subst hPP
    exact hQu Q' ⟨hQ'S, hxQ'⟩
  · intro Q hQ
    obtain ⟨⟨P, hPm⟩, -, hQS⟩ := Finset.mem_biUnion.1 hQ
    exact (hS2 P hPm Q hQS).2.2.2

/-- The partition, as a finite set of pairs (base point, direction). -/
theorem main (n : ℕ) (U : Submodule K (X n)) (p : X n) : ∀ gs : List Gate,
    (∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = GateOp.not ∧ g.inputs.length = 1)) →
    ∃ parts : Finset (X n × Submodule K (X n)), parts.card ≤ 2 ^ cost gs ∧
      (∀ P ∈ parts, P.1 - p ∈ U ∧ P.2 ≤ U ∧
        Module.finrank K U ≤ Module.finrank K P.2 + cost gs) ∧
      (∀ x : X n, x - p ∈ U → ∃! P, P ∈ parts ∧ x - P.1 ∈ P.2) ∧
      (∀ P ∈ parts, Aff n gs P.1 P.2) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨{(p, U)}, by simp [cost], ?_, ?_, ?_⟩
    · intro P hP
      rw [Finset.mem_singleton] at hP; subst hP
      exact ⟨by simp, le_refl _, Nat.le_add_right _ _⟩
    · intro x hx
      exact ⟨(p, U), ⟨Finset.mem_singleton_self _, hx⟩, fun Q hQ => Finset.mem_singleton.1 hQ.1⟩
    · intro P hP
      rw [Finset.mem_singleton] at hP; subst hP
      exact aff_nil n p U
  | append_singleton gs g ih =>
    intro hall
    obtain ⟨parts, hcard, hP, hcov, haff⟩ := ih (fun g' hg' => hall g' (List.mem_append_left _ hg'))
    rcases hall g (by simp) with ⟨hop, hlen⟩ | hfree
    · have := glue U p gs g (cost gs) 1 parts hcard hP hcov
        (fun P hPm => split_paid gs g P.1 P.2 hop hlen (haff P hPm))
      rw [cost_snoc_paid gs g hop]
      exact this
    · have hno : ¬ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
        rcases hfree with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
      have := glue U p gs g (cost gs) 0 parts hcard hP hcov
        (fun P hPm => keep gs g P.1 P.2 0 (aff_snoc gs g P.1 P.2 (haff P hPm)
          (new_free gs g P.1 P.2 (haff P hPm) hfree)))
      rw [cost_snoc_free gs g hno]
      simpa using this

end PEqualNP.Outside.L_lib_573

theorem PEqualNP.Outside.L_lib_573 : 
  ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
    let K := ZMod 2
    let X := Fin n → K
    let input := fun x : X => List.ofFn (fun i : Fin n => decide (x i = 1))
    let cost := C.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _))
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
    (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) →
    ∀ (U : Submodule K X) (p : X), ∃ (m : ℕ) (base : Fin m → X) (dir : Fin m → Submodule K X),
      m ≤ 2^cost ∧ (∀ j, base j - p ∈ U ∧ dir j ≤ U ∧
        Module.finrank K U ≤ Module.finrank K (dir j) + cost) ∧
      (∀ x : X, x-p ∈ U → ∃! j : Fin m, x-base j ∈ dir j) ∧
      ∀ (part : Fin m) (wire : ℕ), ∃ (weight : X) (offset : K),
        ∀ point : X, point-base part ∈ dir part →
          (C.wires (input point)).getD wire false = decide (dotProduct weight point + offset = 1) := by
  intro n C
  dsimp only
  intro _ hg U p
  obtain ⟨parts, hcard, hP, hcov, haff⟩ := PEqualNP.Outside.L_lib_573.main n U p C.gates hg
  refine ⟨parts.card, fun j => (parts.equivFin.symm j).1.1, fun j => (parts.equivFin.symm j).1.2,
    hcard, ?_, ?_, ?_⟩
  · intro j
    exact hP _ (parts.equivFin.symm j).2
  · intro x hx
    obtain ⟨P, ⟨hPm, hxP⟩, hPu⟩ := hcov x hx
    refine ⟨parts.equivFin ⟨P, hPm⟩, by simpa using hxP, ?_⟩
    intro j hj
    have e := hPu _ ⟨(parts.equivFin.symm j).2, hj⟩
    exact (Equiv.symm_apply_eq _).1 (Subtype.ext e)
  · intro part wire
    exact haff _ (parts.equivFin.symm part).2 wire
