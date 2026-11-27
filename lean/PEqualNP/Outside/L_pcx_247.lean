import PEqualNP.Defs
import Mathlib.Combinatorics.Extremal.RuzsaSzemeredi
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_pcx_247_aux.PCX247Forward

open SimpleGraph

def possible (n k : ℕ) : Prop :=
  ∃ code : (Fin n → Bool) → Fin 3 → (Fin k → Bool),
    ∀ word : Fin 3 → (Fin n → Bool),
      (∀ e : Fin 3, code (word e) e = code (word (e+1)) e) →
      ∀ p : Fin 3, word p = word 0

private abbrev Triangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] := ↥(G.cliqueFinset 3)

private abbrev Label {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] := Triangle G × Equiv.Perm (Fin 3)

section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private noncomputable def triangleOrder (t : Triangle G) : (↥t.val) ≃ Fin 3 :=
  t.val.equivFinOfCardEq (SimpleGraph.mem_cliqueFinset_iff.mp t.property).card_eq

private noncomputable def vertex (t : Label G) (i : Fin 3) : V :=
  ((triangleOrder G t.1).symm (t.2 i)).val

private theorem vertex_mem (t : Label G) (i : Fin 3) : vertex G t i ∈ t.1.val :=
  ((triangleOrder G t.1).symm (t.2 i)).property

private theorem vertex_injective (t : Label G) : Function.Injective (vertex G t) := by
  intro i j eq
  exact t.2.injective ((triangleOrder G t.1).symm.injective (Subtype.ext eq))

private theorem vertex_adj (t : Label G) {i j : Fin 3} (different : i ≠ j) :
    G.Adj (vertex G t i) (vertex G t j) :=
  (SimpleGraph.mem_cliqueFinset_iff.mp t.1.property).isClique
    (vertex_mem G t i) (vertex_mem G t j) (fun same => different (vertex_injective G t same))

private theorem vertex_surjects_on_triangle (t : Label G) (x : V) (hx : x ∈ t.1.val) :
    ∃ i : Fin 3, vertex G t i = x := by
  let x' : ↥t.1.val := ⟨x, hx⟩
  refine ⟨t.2.symm (triangleOrder G t.1 x'), ?_⟩
  simp [vertex, x']

private theorem eq_of_vertices (a b : Label G)
    (same : ∀ i : Fin 3, vertex G a i = vertex G b i) : a = b := by
  have sub (c d : Label G) (h : ∀ i : Fin 3, vertex G c i = vertex G d i) :
      c.1.val ⊆ d.1.val := by
    intro x hx
    obtain ⟨i, hi⟩ := vertex_surjects_on_triangle G c x hx
    rw [← hi, h i]
    exact vertex_mem G d i
  have possibleEq : a.1 = b.1 := Subtype.ext
    (Finset.Subset.antisymm (sub a b same) (sub b a (fun i => (same i).symm)))
  rcases a with ⟨t, p⟩
  rcases b with ⟨u, q⟩
  change t = u at possibleEq
  subst u
  have samePermutation : p = q :=
    Equiv.ext (fun i => (triangleOrder G t).symm.injective (Subtype.ext (same i)))
  subst q
  rfl

omit [Fintype V] [DecidableRel G.Adj] in
private theorem common_neighbor_unique (linear : G.LocallyLinear)
    {x y a b : V} (xy : G.Adj x y)
    (xa : G.Adj x a) (ya : G.Adj y a) (xb : G.Adj x b) (yb : G.Adj y b) : a = b := by
  let first : Finset V := {x, y, a}
  let second : Finset V := {x, y, b}
  have hfirst : first ∈ G.cliqueSet 3 := mem_cliqueSet_iff.mpr
    (is3Clique_triple_iff.mpr ⟨xy, xa, ya⟩)
  have hsecond : second ∈ G.cliqueSet 3 := mem_cliqueSet_iff.mpr
    (is3Clique_triple_iff.mpr ⟨xy, xb, yb⟩)
  have equal : first = second := by
    by_contra different
    have singleton := linear.edgeDisjointTriangles hfirst hsecond different
    exact xy.ne (singleton (by simp [first, second] : x ∈ (first ∩ second : Set V))
      (by simp [first, second] : y ∈ (first ∩ second : Set V)))
  have member : a ∈ second := by
    rw [← equal]
    simp [first]
  simpa [second, xa.ne.symm, ya.ne.symm] using member

private theorem consistent_labels (linear : G.LocallyLinear) (r : Fin 3 → Label G)
    (compatible : ∀ e : Fin 3, vertex G (r e) e = vertex G (r (e+1)) e) :
    ∀ p : Fin 3, r p = r 0 := by
  let a := r 0
  let b := r 1
  let c := r 2
  let x := vertex G a 0
  let y := vertex G b 1
  let z := vertex G c 2
  have ab : vertex G a 0 = vertex G b 0 := compatible 0
  have bc : vertex G b 1 = vertex G c 1 := compatible 1
  have ca : vertex G c 2 = vertex G a 2 := compatible 2
  have adj01 (d : Label G) : G.Adj (vertex G d 0) (vertex G d 1) := vertex_adj G d (by decide)
  have adj02 (d : Label G) : G.Adj (vertex G d 0) (vertex G d 2) := vertex_adj G d (by decide)
  have adj12 (d : Label G) : G.Adj (vertex G d 1) (vertex G d 2) := vertex_adj G d (by decide)
  have xy : G.Adj x y := by
    change G.Adj (vertex G a 0) (vertex G b 1)
    rw [ab]
    exact adj01 b
  have xz : G.Adj x z := by
    change G.Adj (vertex G a 0) (vertex G c 2)
    rw [ca]
    exact adj02 a
  have yz : G.Adj y z := by
    change G.Adj (vertex G b 1) (vertex G c 2)
    rw [bc]
    exact adj12 c
  have a1 : vertex G a 1 = y := by
    refine common_neighbor_unique G linear xz (adj01 a) ?_ xy yz.symm
    change G.Adj (vertex G c 2) (vertex G a 1)
    rw [ca]
    exact (adj12 a).symm
  have b2 : vertex G b 2 = z := by
    refine common_neighbor_unique G linear xy ?_ (adj12 b) xz yz
    change G.Adj (vertex G a 0) (vertex G b 2)
    rw [ab]
    exact adj02 b
  have c0 : vertex G c 0 = x := by
    refine common_neighbor_unique G linear yz ?_ (adj02 c).symm xy.symm xz.symm
    change G.Adj (vertex G b 1) (vertex G c 0)
    rw [bc]
    exact (adj01 c).symm
  have ba : b = a := by
    apply eq_of_vertices G
    intro i
    fin_cases i
    · exact ab.symm
    · exact a1.symm
    · exact b2.trans ca
  have ca' : c = a := by
    apply eq_of_vertices G
    intro i
    fin_cases i
    · exact c0
    · exact bc.symm.trans a1.symm
    · exact ca
  intro p
  fin_cases p
  · rfl
  · exact ba
  · exact ca'

end

theorem possible_of_ruzsaSzemeredi (n k : ℕ) (bound : 2^n ≤ 6 * ruzsaSzemerediNumberNat (2^k)) :
    possible n k := by
  classical
  obtain ⟨G, dec, hcount, linear⟩ := ruzsaSzemerediNumber_spec (α := Fin k → Bool)
  let _ : DecidableRel G.Adj := dec
  have words (m : ℕ) : Fintype.card (Fin m → Bool) = 2^m := by simp
  have triangles : (G.cliqueFinset 3).card = ruzsaSzemerediNumberNat (2^k) :=
    hcount.trans (by rw [← ruzsaSzemerediNumberNat_card, words])
  have six : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    decide
  have cardLabels : Fintype.card (Label G) = 6 * ruzsaSzemerediNumberNat (2^k) := by
    change Fintype.card (Triangle G × Equiv.Perm (Fin 3)) = _
    rw [Fintype.card_prod, six, Fintype.card_coe, triangles, Nat.mul_comm]
  obtain ⟨labels⟩ : Nonempty ((Fin n → Bool) ↪ Label G) :=
    Function.Embedding.nonempty_iff_card_le.mpr (by simpa [words, cardLabels] using bound)
  refine ⟨fun w e => vertex G (labels w) e, ?_⟩
  intro word compatible p
  exact labels.injective (consistent_labels G linear (fun e => labels (word e)) compatible p)


end PEqualNP.Outside.L_pcx_247_aux.PCX247Forward

namespace PEqualNP.Outside.L_pcx_247_aux.PcxCodesToGraph

open SimpleGraph SimpleGraph.TripartiteFromTriangles

abbrev CodeSound {W V : Type*} (code : W → Fin 3 → V) : Prop :=
  ∀ word : Fin 3 → W,
    (∀ e : Fin 3, code (word e) e = code (word (e + 1)) e) →
    ∀ p : Fin 3, word p = word 0

abbrev possible (n k : Nat) : Prop :=
  ∃ code : (Fin n → Bool) → Fin 3 → (Fin k → Bool), CodeSound code

abbrev Vertices (k : Nat) :=
  (Fin k → Bool) ⊕ (Fin k → Bool) ⊕ (Fin k → Bool)

theorem vertex_count (k : Nat) : Fintype.card (Vertices k) = 3 * 2 ^ k := by
  simp [Vertices]
  omega

private theorem cyclic_words {W V : Type*} {code : W → Fin 3 → V} (sound : CodeSound code)
    {x y z : W} (h0 : code x 0 = code y 0) (h1 : code y 1 = code z 1)
    (h2 : code z 2 = code x 2) : y = x ∧ z = x := by
  let word (e : Fin 3) := if e = 0 then x else if e = 1 then y else z
  have hs : ∀ e : Fin 3, code (word e) e = code (word (e + 1)) e := by
    intro e
    fin_cases e
    · exact h0
    · exact h1
    · exact h2
  exact ⟨sound word hs 1, sound word hs 2⟩

private theorem channel01 {W V : Type*} {code : W → Fin 3 → V} (sound : CodeSound code)
    {x y : W} (h0 : code x 0 = code y 0) (h1 : code x 1 = code y 1) :
    x = y :=
  (cyclic_words sound h0 h1.symm (rfl : code x 2 = code x 2)).1.symm

private theorem channel02 {W V : Type*} {code : W → Fin 3 → V} (sound : CodeSound code)
    {x y : W} (h0 : code x 0 = code y 0) (h2 : code x 2 = code y 2) :
    x = y :=
  (cyclic_words sound h0 (rfl : code y 1 = code y 1) h2.symm).1.symm

private theorem channel12 {W V : Type*} {code : W → Fin 3 → V} (sound : CodeSound code)
    {x y : W} (h1 : code x 1 = code y 1) (h2 : code x 2 = code y 2) :
    x = y :=
  (cyclic_words sound (rfl : code x 0 = code x 0) h1 h2.symm).2.symm

/-- The accepted words give exactly one explicit triangle each.
Repeated edges and accidental triangles would give an inconsistent cycle. -/
theorem graph_of_possible (n k : Nat) (h : possible n k) :
    ∃ (G : SimpleGraph (Vertices k)) (_ : DecidableRel G.Adj),
      (G.cliqueFinset 3).card = 2 ^ n ∧ G.LocallyLinear := by
  classical
  obtain ⟨code, sound⟩ := h
  let W := Fin n → Bool
  let V := Fin k → Bool
  let coords (w : W) : V × V × V := (code w 0, code w 1, code w 2)
  have coordInj : Function.Injective coords := by
    intro x y eq
    exact channel01 sound (congrArg Prod.fst eq) (congrArg (fun t => t.2.1) eq)
  let emb : W ↪ V × V × V := ⟨coords, coordInj⟩
  let tris := Finset.univ.map emb
  have witness {a b c : V} (h : (a,b,c) ∈ tris) :
      ∃ w : W, code w 0 = a ∧ code w 1 = b ∧ code w 2 = c := by
    obtain ⟨w, _, eq⟩ := Finset.mem_map.mp h
    exact ⟨w, congrArg Prod.fst eq, congrArg (fun t => t.2.1) eq, congrArg (fun t => t.2.2) eq⟩
  haveI : ExplicitDisjoint tris := by
    constructor
    · intro a b c a' h h'
      obtain ⟨x, x0, x1, x2⟩ := witness h
      obtain ⟨y, y0, y1, y2⟩ := witness h'
      have eq := channel12 sound (x1.trans y1.symm) (x2.trans y2.symm)
      exact x0.symm.trans ((congrArg (fun w => code w 0) eq).trans y0)
    · intro a b c b' h h'
      obtain ⟨x, x0, x1, x2⟩ := witness h
      obtain ⟨y, y0, y1, y2⟩ := witness h'
      have eq := channel02 sound (x0.trans y0.symm) (x2.trans y2.symm)
      exact x1.symm.trans ((congrArg (fun w => code w 1) eq).trans y1)
    · intro a b c c' h h'
      obtain ⟨x, x0, x1, x2⟩ := witness h
      obtain ⟨y, y0, y1, y2⟩ := witness h'
      have eq := channel01 sound (x0.trans y0.symm) (x1.trans y1.symm)
      exact x2.symm.trans ((congrArg (fun w => code w 2) eq).trans y2)
  haveI : NoAccidental tris := by
    constructor
    · intro a a' b b' c c' ha hb hc
      obtain ⟨x, x0, x1, x2⟩ := witness ha
      obtain ⟨y, y0, y1, y2⟩ := witness hb
      obtain ⟨z, z0, z1, z2⟩ := witness hc
      have agree := cyclic_words sound (y0.trans z0.symm) (z1.trans x1.symm) (x2.trans y2.symm)
      exact Or.inr (Or.inl (x1.symm.trans ((congrArg (fun w => code w 1) agree.2).trans y1)))
  refine ⟨graph tris, inferInstance, ?_, locallyLinear tris⟩
  rw [card_triangles]
  simp [tris, W]

theorem possible_le_rs (n k : Nat) (h : possible n k) :
    2 ^ n ≤ ruzsaSzemerediNumberNat (3 * 2 ^ k) := by
  classical
  obtain ⟨G, dec, hcount, hG⟩ := graph_of_possible n k h
  rw [← vertex_count k, ruzsaSzemerediNumberNat_card, ← hcount]
  exact @SimpleGraph.LocallyLinear.le_ruzsaSzemerediNumber (Vertices k) _ _ G dec hG


end PEqualNP.Outside.L_pcx_247_aux.PcxCodesToGraph

namespace PEqualNP.Outside.L_pcx_247_aux.Pcx247

open SimpleGraph

theorem rs_eventually_lt_mul_sq (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ v : ℕ, K ≤ v → (ruzsaSzemerediNumberNat v : ℝ) < ε * (v : ℝ)^2 := by
  classical
  let δ := triangleRemovalBound ε
  have hδ : 0 < δ := triangleRemovalBound_pos hε
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ)
  refine ⟨K, ?_⟩
  intro v hv
  have hvReal : 1 / δ < (v : ℝ) := hK.trans_le (by exact_mod_cast hv)
  have hvPos : 0 < (v : ℝ) := lt_of_le_of_lt (by positivity : 0 ≤ 1 / δ) hvReal
  have hproduct : 1 < δ * (v : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hvReal
  apply lt_of_not_ge
  intro hLarge
  obtain ⟨G, adjDec, hcount, hlinear⟩ := ruzsaSzemerediNumber_spec (α := Fin v)
  letI : DecidableRel G.Adj := adjDec
  change (G.cliqueFinset 3).card = ruzsaSzemerediNumberNat v at hcount
  have hfar : G.FarFromTriangleFree ε := hlinear.edgeDisjointTriangles.farFromTriangleFree (by
    simpa only [Fintype.card_fin, Nat.cast_pow, hcount] using hLarge)
  have hTriangle := hfar.le_card_cliqueFinset
  have hEdge : G.edgeFinset.card ≤ v.choose 2 := by
    simpa only [Fintype.card_fin] using G.card_edgeFinset_le_card_choose_two
  have hChoose : v.choose 2 ≤ v ^ 2 := Nat.choose_le_pow v 2
  have hTri3 : 3 * (G.cliqueFinset 3).card ≤ G.edgeFinset.card :=
    hlinear.edgeDisjointTriangles.card_edgeFinset_le
  have hTri : (G.cliqueFinset 3).card ≤ v ^ 2 := by omega
  have hSq : (v : ℝ)^2 < δ * (v : ℝ)^3 := by
    calc
      _ = 1 * (v : ℝ)^2 := by rw [one_mul]
      _ < (δ * (v : ℝ)) * (v : ℝ)^2 :=
        mul_lt_mul_of_pos_right hproduct (pow_pos hvPos 2)
      _ = _ := by ring
  exact hSq.not_ge (by
    have hTriReal : ((G.cliqueFinset 3).card : ℝ) ≤ (v : ℝ)^2 := by exact_mod_cast hTri
    exact (show δ * (v : ℝ)^3 ≤ ((G.cliqueFinset 3).card : ℝ) by
      simpa only [Fintype.card_fin, δ] using hTriangle).trans hTriReal)

theorem unbounded_deficit_of_reverse_bound (possible : ℕ → ℕ → Prop)
    (bound : ∀ n k : ℕ, possible n k → 2^n ≤ ruzsaSzemerediNumberNat (3 * 2^k)) :
    ∀ d : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ, possible n k → n+d < 2*k := by
  intro d
  let ε : ℝ := 1 / (9 * (2:ℝ)^d)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨K, hK⟩ := rs_eventually_lt_mul_sq ε hε
  refine ⟨K, ?_⟩
  intro k hk n hn
  have hkpow : k ≤ 2^k := Nat.le_of_lt k.lt_two_pow_self
  have hsize : K ≤ 3 * 2^k := by omega
  have hNat := bound n k hn
  have hPow : (2:ℝ)^n ≤ (ruzsaSzemerediNumberNat (3 * 2^k) : ℝ) := by exact_mod_cast hNat
  have hlt : (2:ℝ)^n < ε * (↑(3 * 2^k : ℕ) : ℝ)^2 := hPow.trans_lt (hK _ hsize)
  have scaled : ε * (↑(3 * 2^k : ℕ) : ℝ)^2 * (2:ℝ)^d = (2:ℝ)^(2*k) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, ε, one_div]
    rw [Nat.mul_comm 2 k, pow_mul]
    have hne : (9 * (2:ℝ)^d) ≠ 0 := by positivity
    calc
      _ = ((9 * (2:ℝ)^d)⁻¹ * (9 * (2:ℝ)^d)) * ((2:ℝ)^k)^2 := by ring
      _ = _ := by rw [inv_mul_cancel₀ hne, one_mul]
  have hp : (2:ℝ)^(n+d) < (2:ℝ)^(2*k) := by
    rw [pow_add, ← scaled]
    exact mul_lt_mul_of_pos_right hlt (by positivity)
  exact (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hp


end PEqualNP.Outside.L_pcx_247_aux.Pcx247

namespace PEqualNP.Outside.L_pcx_247

private theorem ratePowerBound (k : ℕ) (hk : 5 ≤ k) :
    2 ^ (2 * k - 20 * (Nat.sqrt k + 1)) ≤
      6 * ruzsaSzemerediNumberNat (2 ^ k) := by
  let Q : ℕ := 2 ^ k
  let m : ℕ := Nat.sqrt k + 1
  let u : ℕ := (Q - 3) / 6
  have hQ : 32 ≤ Q := by
    change 2 ^ 5 ≤ 2 ^ k
    exact Nat.pow_le_pow_right (by decide) hk
  have hQR : (32 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have huLowN : Q ≤ 12 * u := by dsimp [u]; omega
  have huPos : (0 : ℝ) < (u : ℝ) := by
    have h : 0 < u := by omega
    exact_mod_cast h
  have huLe : u ≤ Q := by dsimp [u]; omega
  have huCoef : (Q : ℝ) / 12 ≤ (u : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).2
    exact_mod_cast (show Q ≤ u * 12 by simpa only [Nat.mul_comm] using huLowN)
  have hQCoef : (Q : ℝ) / 4 ≤ (Q : ℝ) / 3 - 2 := by linarith
  have hproduct : (Q : ℝ) ^ 2 / 64 ≤ ((Q : ℝ) / 3 - 2) * (u : ℝ) := by
    calc
      (Q : ℝ) ^ 2 / 64 ≤ (Q : ℝ) / 4 * ((Q : ℝ) / 12) := by
        nlinarith [sq_nonneg (Q : ℝ)]
      _ ≤ _ := mul_le_mul hQCoef huCoef (by positivity) (by linarith)
  have hlogHi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogLo : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogQ : Real.log (Q : ℝ) = (k : ℝ) * Real.log 2 := by
    simp [Q, Real.log_pow]
  have hlogu : Real.log (u : ℝ) ≤ (k : ℝ) := by
    calc
      Real.log (u : ℝ) ≤ Real.log (Q : ℝ) := Real.log_le_log huPos (by exact_mod_cast huLe)
      _ = (k : ℝ) * Real.log 2 := hlogQ
      _ ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left hlogHi (by positivity)
      _ = (k : ℝ) := mul_one _
  have hmSquare : k ≤ m ^ 2 := by
    simpa [m, Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt' k).le
  have hsqrt : Real.sqrt (Real.log (u : ℝ)) ≤ (m : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, hlogu.trans (by exact_mod_cast hmSquare)⟩
  have hexp : Real.exp (-4 * (m : ℝ)) ≤ Real.exp (-4 * Real.sqrt (Real.log (u : ℝ))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hLower : (Q : ℝ) ^ 2 / 64 * Real.exp (-4 * (m : ℝ)) ≤
      (ruzsaSzemerediNumberNat Q : ℝ) := by
    calc
      _ ≤ ((Q : ℝ) / 3 - 2) * (u : ℝ) * Real.exp (-4 * Real.sqrt (Real.log (u : ℝ))) :=
        mul_le_mul hproduct hexp (by positivity) (mul_nonneg (by linarith) (by positivity))
      _ ≤ _ := by simpa [u] using ruzsaSzemerediNumberNat_lower_bound Q
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by
    have h : 1 ≤ m := by dsimp [m]; omega
    exact_mod_cast h
  have hscale : (64 : ℝ) ≤ (2 : ℝ) ^ (20 * m) * Real.exp (-4 * (m : ℝ)) := by
    calc
      (64 : ℝ) = Real.exp (((6 : ℕ) : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ Real.exp (((20 * m : ℕ) : ℝ) * Real.log 2 + (-4) * (m : ℝ)) := by
        apply Real.exp_le_exp.mpr
        push_cast
        have hmul := mul_le_mul_of_nonneg_left hlogLo (show (0 : ℝ) ≤ 20 * (m : ℝ) by positivity)
        linarith
      _ = _ := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  change 2 ^ (2 * k - 20 * m) ≤ 6 * ruzsaSzemerediNumberNat Q
  by_cases hcost : 20 * m ≤ 2 * k
  · let e := 2 * k - 20 * m
    have he : e + 20 * m = 2 * k := Nat.sub_add_cancel hcost
    have hpow : (2 : ℝ) ^ e * (2 : ℝ) ^ (20 * m) = (Q : ℝ) ^ 2 := by
      rw [← pow_add, he, show 2 * k = k * 2 by omega, pow_mul]
      simp [Q]
    have hReal : (2 : ℝ) ^ e ≤ (ruzsaSzemerediNumberNat Q : ℝ) := by
      calc
        (2 : ℝ) ^ e = (2 : ℝ) ^ e * 64 / 64 := by ring
        _ ≤ (2 : ℝ) ^ e * ((2 : ℝ) ^ (20 * m) * Real.exp (-4 * (m : ℝ))) / 64 := by
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity)) (by norm_num)
        _ = (Q : ℝ) ^ 2 / 64 * Real.exp (-4 * (m : ℝ)) := by
          rw [← mul_assoc, hpow]
          ring
        _ ≤ _ := hLower
    have hNat : 2 ^ e ≤ ruzsaSzemerediNumberNat Q := by exact_mod_cast hReal
    exact hNat.trans (by omega)
  · have hRpos : (0 : ℝ) < (ruzsaSzemerediNumberNat Q : ℝ) :=
      lt_of_lt_of_le (by positivity) hLower
    have hNpos : 0 < ruzsaSzemerediNumberNat Q := by exact_mod_cast hRpos
    rw [show 2 * k - 20 * m = 0 by omega, pow_zero]
    omega

theorem rateFromFiniteLower {possible : ℕ → ℕ → Prop}
    (fromFiniteLower : ∀ n k : ℕ, 2 ^ n ≤ 6 * ruzsaSzemerediNumberNat (2 ^ k) → possible n k) :
    ∃ C K : ℕ, ∀ k : ℕ, K ≤ k → possible (2 * k - C * (Nat.sqrt k + 1)) k := by
  refine ⟨20, 5, ?_⟩
  intro k hk
  exact fromFiniteLower _ k (ratePowerBound k hk)

end PEqualNP.Outside.L_pcx_247

theorem PEqualNP.Outside.L_pcx_247 :
  let possible := fun (n k : ℕ) =>
    ∃ code : (Fin n → Bool) → Fin 3 → (Fin k → Bool),
      ∀ word : Fin 3 → (Fin n → Bool),
        (∀ e : Fin 3, code (word e) e = code (word (e+1)) e) →
        ∀ p : Fin 3, word p = word 0
  (∀ n k : ℕ,
    (2^n ≤ 6 * ruzsaSzemerediNumberNat (2^k) → possible n k) ∧
    (possible n k → 2^n ≤ ruzsaSzemerediNumberNat (3 * 2^k))) ∧
  (∀ d : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ, possible n k → n+d < 2*k) ∧
  ∃ C K : ℕ, ∀ k : ℕ, K ≤ k → possible (2*k - C*(Nat.sqrt k + 1)) k := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro n k
    exact ⟨PEqualNP.Outside.L_pcx_247_aux.PCX247Forward.possible_of_ruzsaSzemeredi n k,
      PEqualNP.Outside.L_pcx_247_aux.PcxCodesToGraph.possible_le_rs n k⟩
  · exact PEqualNP.Outside.L_pcx_247_aux.Pcx247.unbounded_deficit_of_reverse_bound
      PEqualNP.Outside.L_pcx_247_aux.PcxCodesToGraph.possible
      PEqualNP.Outside.L_pcx_247_aux.PcxCodesToGraph.possible_le_rs
  · exact PEqualNP.Outside.L_pcx_247.rateFromFiniteLower
      (possible := PEqualNP.Outside.L_pcx_247_aux.PCX247Forward.possible)
      PEqualNP.Outside.L_pcx_247_aux.PCX247Forward.possible_of_ruzsaSzemeredi
