import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_pcx_365
import PEqualNP.ProofComplexity.L043
import PEqualNP.ProofComplexity.L059

namespace PEqualNP.Outside.L_pcx_366_aux

open PEqualNP.CircuitLowerBounds PEqualNP.ProofComplexity PEqualNP.Expanders
  PEqualNP.MetaComplexity.NestedCover

private lemma funGraphPHP_nonempty {n : ℕ} (G : BipGraph (n + 1) n) :
    (funGraphPHP G).Nonempty := by
  refine ⟨Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = (0 : Fin (n + 1)) ∧ l.2 = true), ?_⟩
  exact Or.inl (Or.inl ⟨0, rfl⟩)

private lemma lower_bound_on_expander (b s₀ n : ℕ) (hs₀ : 0 < s₀) (G : BipGraph (n + 1) n)
    (hLd : LeftDegLe G b) (hE : IsBdryExpander G (n / s₀) 2)
    (w : ℕ) (hw : w = max b 2)
    (hn2 : 4 * (s₀ * w) + s₀ ≤ n)
    (C : ℕ) (hC : 64 * (16 * s₀ * w ^ 2) * s₀ * w ≤ C)
    (a k : ℕ) (extra : Set (Clause (GEdge G ⊕ Fin a)))
    (H : Circuit) (pick : Fin a → Fin (2 + Fintype.card (GEdge G) + H.size))
    (hk : 1 ≤ k)
    (hallow : ReadsBack (2 + Fintype.card (GEdge G)) H ∧
      ∀ g ∈ H.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
        g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))
    (hsat : ∀ x : GEdge G → Bool,
      Satisfies (Sum.elim x (fun i : Fin a =>
        (H.wires ([false, true] ++ List.ofFn (fun j : Fin (Fintype.card (GEdge G)) =>
          x ((Fintype.equivFin (GEdge G)).symm j)))).getD (pick i).val false)) extra)
    (π : List (LinKLine (GEdge G ⊕ Fin a)))
    (hπ : IsLinKRefutation k
      (Set.image (fun cl : Clause (GEdge G) =>
        cl.image (fun l => ((Sum.inl l.1 : GEdge G ⊕ Fin a), l.2))) (funGraphPHP G) ∪ extra) π) :
    let t := H.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _))
    n ≤ C ^ k * (t + Nat.clog 2 (π.length + 1) + 1) := by
  intro t
  set B := 16 * s₀ * w ^ 2 with hB
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hB1 : 64 ≤ B := by
    rw [hB]
    have : 4 ≤ w ^ 2 := by nlinarith
    nlinarith
  have hsw1 : 2 ≤ s₀ * w := by nlinarith
  have hC_pos : 2 ≤ C := by nlinarith
  by_cases hn1 : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n
  · obtain ⟨τ, hτ, hτlen⟩ :=
      PEqualNP.Outside.L_pcx_365 (GEdge G) (Fintype.card (GEdge G)) a k
        (Fintype.equivFin (GEdge G)).symm (funGraphPHP G) extra H pick
        (funGraphPHP_nonempty G) hk hallow.1 hallow.2 hsat π hπ
    have hL : PEqualNP.ProofComplexity.LinKFinal.StmtLinK :=
      PEqualNP.ProofComplexity.LinKWire.general PEqualNP.ProofComplexity.LinKSim.simulation_refutation
    have hgb := PEqualNP.ProofComplexity.LinKGrow.graph_bound hL b s₀ n k w hw hs₀ hk G hLd hE
      hn1 hn2 τ hτ
    set m := Nat.clog 2 (π.length + 1)
    have hclog : π.length + 1 ≤ 2 ^ m := Nat.le_pow_clog (by omega) (π.length + 1)
    have hlen_nat : τ.length ≤ 2 ^ (t + m + 1) := by
      have hmin : min (Fintype.card (GEdge G)) t ≤ t := min_le_right _ _
      have h1 : 2 * π.length + 1 ≤ 2 ^ (m + 1) := by
        rw [pow_succ']
        omega
      calc τ.length ≤ (2 * π.length + 1) * 2 ^ (min (Fintype.card (GEdge G)) t) := hτlen
        _ ≤ 2 ^ (m + 1) * 2 ^ t :=
            Nat.mul_le_mul h1 (Nat.pow_le_pow_right (by omega) hmin)
        _ = 2 ^ (t + m + 1) := by rw [← pow_add]; congr 1; omega
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hexp_ub : (τ.length : ℝ) ≤ Real.exp ((t + m + 1 : ℕ) : ℝ) := by
      calc (τ.length : ℝ) ≤ ((2 ^ (t + m + 1) : ℕ) : ℝ) := by exact_mod_cast hlen_nat
        _ = (2 : ℝ) ^ (t + m + 1) := by push_cast; rfl
        _ ≤ (Real.exp 1) ^ (t + m + 1) := pow_le_pow_left₀ (by norm_num) h2e _
        _ = Real.exp (((t + m + 1 : ℕ) : ℝ) * 1) := by rw [← Real.exp_nat_mul]
        _ = Real.exp ((t + m + 1 : ℕ) : ℝ) := by ring_nf
    have hle_exp := le_trans hgb hexp_ub
    have hle_arg : (1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w) * n ≤
        ((t + m + 1 : ℕ) : ℝ) := Real.exp_le_exp.mp hle_exp
    have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
    have hDpos : (0 : ℝ) < (32 * (k : ℝ) * s₀ * w) := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsR : (0 : ℝ) < s₀ := by exact_mod_cast hs₀
      have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
      positivity
    have hBcast : (16 * (s₀ : ℝ) * (w : ℝ) ^ 2) = (B : ℝ) := by rw [hB]; push_cast; rfl
    rw [hBcast, one_div, inv_pow] at hle_arg
    have hmul : (n : ℝ) ≤ (B : ℝ) ^ k * (32 * (k : ℝ) * s₀ * w) * ((t + m + 1 : ℕ) : ℝ) := by
      have hden : (0 : ℝ) < (B : ℝ) ^ k * (32 * (k : ℝ) * s₀ * w) := by positivity
      have hrew : ((B : ℝ) ^ k)⁻¹ / (32 * (k : ℝ) * s₀ * w) * (n : ℝ) =
          (n : ℝ) / ((B : ℝ) ^ k * (32 * (k : ℝ) * s₀ * w)) := by
        field_simp
      rw [hrew, div_le_iff₀ hden] at hle_arg
      linarith
    have hnat : n ≤ B ^ k * (32 * k * s₀ * w) * (t + m + 1) := by
      have : ((n : ℕ) : ℝ) ≤ ((B ^ k * (32 * k * s₀ * w) * (t + m + 1) : ℕ) : ℝ) := by
        push_cast at hmul ⊢
        exact hmul
      exact_mod_cast this
    have hpow_le : B ^ k * (32 * k * s₀ * w) ≤ C ^ k := by
      have hk2 : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      have h32 : 32 * s₀ * w ≤ (32 * s₀ * w) ^ k :=
        Nat.le_self_pow (by omega) _
      calc B ^ k * (32 * k * s₀ * w)
          = B ^ k * k * (32 * s₀ * w) := by ring
        _ ≤ B ^ k * 2 ^ k * (32 * s₀ * w) ^ k :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hk2) h32
        _ = (64 * B * s₀ * w) ^ k := by
            rw [← mul_pow, ← mul_pow]; congr 1; ring
        _ ≤ C ^ k := Nat.pow_le_pow_left hC k
    calc n ≤ B ^ k * (32 * k * s₀ * w) * (t + m + 1) := hnat
      _ ≤ C ^ k * (t + m + 1) := Nat.mul_le_mul_right _ hpow_le
  · have hlt : n < 2 * (s₀ * w) * (16 * k + 4 * w) := by omega
    have h1 : 16 * k + 4 * w ≤ (16 + 4 * w) * k := by nlinarith
    have hk2 : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    have hCk : 2 * (s₀ * w) * (16 + 4 * w) * k ≤ C ^ k := by
      have hC_half : 2 * (s₀ * w) * (16 + 4 * w) ≤ (C / 2) ^ k := by
        have hle : 2 * (s₀ * w) * (16 + 4 * w) ≤ C / 2 := by
          have : 2 * (2 * (s₀ * w) * (16 + 4 * w)) ≤ 64 * B * s₀ * w := by
            have : 4 * (16 + 4 * w) ≤ 64 * B := by
              rw [hB]
              have : w ≤ w ^ 2 := by nlinarith
              nlinarith
            nlinarith
          omega
        exact le_trans hle (Nat.le_self_pow (by omega) _)
      calc 2 * (s₀ * w) * (16 + 4 * w) * k
          ≤ (C / 2) ^ k * 2 ^ k := Nat.mul_le_mul hC_half hk2
        _ = (C / 2 * 2) ^ k := (mul_pow _ _ _).symm
        _ ≤ C ^ k := Nat.pow_le_pow_left (by omega) k
    have hn_le : n ≤ C ^ k := by
      calc n ≤ 2 * (s₀ * w) * (16 * k + 4 * w) := le_of_lt hlt
        _ ≤ 2 * (s₀ * w) * ((16 + 4 * w) * k) := Nat.mul_le_mul_left _ h1
        _ = 2 * (s₀ * w) * (16 + 4 * w) * k := by ring
        _ ≤ C ^ k := hCk
    exact le_trans hn_le (Nat.le_mul_of_pos_right _ (by omega))

private def SimpleGate (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)

private lemma simpleGate_len_le {g : Gate} (h : SimpleGate g) : g.inputs.length ≤ 2 := by
  rcases h with ⟨_, h2⟩ | ⟨_, h1⟩ <;> omega

private def CValid (m : ℕ) (gs : List Gate) : Prop :=
  ReadsBack m ⟨gs, 0⟩ ∧ ∀ g ∈ gs, SimpleGate g

private lemma cvalid_nil (m : ℕ) : CValid m [] :=
  ⟨fun j hj => by simp at hj, fun _ h => by simp at h⟩

private lemma foldl_wires_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

private lemma foldl_wires_append (gs1 gs2 : List Gate) (x : List Bool) :
    ((gs1 ++ gs2).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (gs1.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) :=
  List.foldl_append

private lemma foldl_wires_prefix (gs : List Gate) (x : List Bool) :
    x <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := by
  induction gs generalizing x with
  | nil => exact List.prefix_rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact (List.prefix_append x _).trans (ih _)

private lemma getD_of_prefix {l1 l2 : List Bool} (hp : l1 <+: l2) {i : ℕ} (hi : i < l1.length) :
    l2.getD i false = l1.getD i false := by
  rcases hp with ⟨t, rfl⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private def wVal (gs : List Gate) (inp : List Bool) (w : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ inp).getD w false

private lemma wVal_prefix {m : ℕ} {gs1 gs2 : List Gate} (hp : gs1 <+: gs2)
    {inp : List Bool} (hinp : inp.length = m) {w : ℕ} (hw : w < m + gs1.length) :
    wVal gs2 inp w = wVal gs1 inp w := by
  rcases hp with ⟨t, rfl⟩
  unfold wVal Circuit.wires
  rw [foldl_wires_append]
  apply getD_of_prefix (foldl_wires_prefix t _)
  rw [foldl_wires_length, hinp]
  exact hw

private lemma wVal_input (gs : List Gate) (inp : List Bool) {w : ℕ} (hw : w < inp.length) :
    wVal gs inp w = inp.getD w false := by
  unfold wVal Circuit.wires
  exact getD_of_prefix (foldl_wires_prefix gs inp) hw

private lemma cvalid_push {m : ℕ} {gs : List Gate} (hv : CValid m gs) (g : Gate)
    (hgOk : SimpleGate g) (hgIn : ∀ i ∈ g.inputs, i < m + gs.length) :
    CValid m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    unfold gateAt at hi
    by_cases hlt : j < gs.length
    · have heq : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [heq] at hi
      exact hv.1 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have heq : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [heq] at hi
      exact hgIn i hi
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hv.2 g' h
    · exact hgOk

private lemma wVal_push {m : ℕ} (gs : List Gate) (g : Gate)
    (inp : List Bool) (hinp : inp.length = m) :
    wVal (gs ++ [g]) inp (m + gs.length) = g.op.eval (g.inputs.map (wVal gs inp)) := by
  unfold wVal Circuit.wires
  rw [foldl_wires_append]
  simp only [List.foldl_cons, List.foldl_nil]
  set base := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp
  have hblen : base.length = m + gs.length := by
    rw [foldl_wires_length, hinp]
  rw [← hblen]
  simp [List.getD_eq_getElem?_getD]

private def mkAnd (m : ℕ) (gs : List Gate) (u v : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.and, [u, v]⟩], m + gs.length)

private def mkOr (m : ℕ) (gs : List Gate) (u v : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.or, [u, v]⟩], m + gs.length)

private def mkNot (m : ℕ) (gs : List Gate) (u : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.not, [u]⟩], m + gs.length)

private def mkFalse (m : ℕ) (gs : List Gate) : List Gate × ℕ :=
  mkAnd m gs 0 0

private lemma mkAnd_spec {m : ℕ} {gs : List Gate} (hv : CValid m gs) {u v : ℕ}
    (hu : u < m + gs.length) (hv' : v < m + gs.length) :
    let r := mkAnd m gs u v
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 1 ∧
    m ≤ r.2 ∧ r.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m → wVal r.1 inp r.2 = (wVal gs inp u && wVal gs inp v) := by
  refine ⟨cvalid_push hv _ (Or.inl ⟨Or.inl rfl, rfl⟩) (by simp [hu, hv']),
    List.prefix_append _ _, by simp [mkAnd], by simp [mkAnd], by simp [mkAnd],
    fun inp hinp => ?_⟩
  unfold mkAnd; dsimp only
  rw [wVal_push gs _ inp hinp]
  simp [GateOp.eval]

private lemma mkOr_spec {m : ℕ} {gs : List Gate} (hv : CValid m gs) {u v : ℕ}
    (hu : u < m + gs.length) (hv' : v < m + gs.length) :
    let r := mkOr m gs u v
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 1 ∧
    m ≤ r.2 ∧ r.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m → wVal r.1 inp r.2 = (wVal gs inp u || wVal gs inp v) := by
  refine ⟨cvalid_push hv _ (Or.inl ⟨Or.inr rfl, rfl⟩) (by simp [hu, hv']),
    List.prefix_append _ _, by simp [mkOr], by simp [mkOr], by simp [mkOr],
    fun inp hinp => ?_⟩
  unfold mkOr; dsimp only
  rw [wVal_push gs _ inp hinp]
  simp [GateOp.eval]

private lemma mkNot_spec {m : ℕ} {gs : List Gate} (hv : CValid m gs) {u : ℕ}
    (hu : u < m + gs.length) :
    let r := mkNot m gs u
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 1 ∧
    m ≤ r.2 ∧ r.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m → wVal r.1 inp r.2 = !(wVal gs inp u) := by
  refine ⟨cvalid_push hv _ (Or.inr ⟨rfl, rfl⟩) (by simp [hu]),
    List.prefix_append _ _, by simp [mkNot], by simp [mkNot], by simp [mkNot],
    fun inp hinp => ?_⟩
  unfold mkNot; dsimp only
  rw [wVal_push gs _ inp hinp]
  simp [GateOp.eval]

private lemma mkFalse_spec {m : ℕ} (hm : 2 ≤ m) {gs : List Gate} (hv : CValid m gs) :
    let r := mkFalse m gs
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 1 ∧
    m ≤ r.2 ∧ r.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m → inp.getD 0 false = false → wVal r.1 inp r.2 = false := by
  unfold mkFalse
  obtain ⟨hv1, hp1, hl1, hge1, hlt1, hval1⟩ := mkAnd_spec hv (u := 0) (v := 0) (by omega) (by omega)
  refine ⟨hv1, hp1, hl1, hge1, hlt1, fun inp hinp h0 => ?_⟩
  rw [hval1 inp hinp, wVal_input gs inp (by omega), h0]
  rfl

private def mkXor (m : ℕ) (gs : List Gate) (u v : ℕ) : List Gate × ℕ :=
  let r1 := mkOr m gs u v
  let r2 := mkAnd m r1.1 u v
  let r3 := mkNot m r2.1 r2.2
  mkAnd m r3.1 r1.2 r3.2

private lemma mkXor_spec {m : ℕ} {gs : List Gate} (hv : CValid m gs) {u v : ℕ}
    (hu : u < m + gs.length) (hv' : v < m + gs.length) :
    let r := mkXor m gs u v
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 4 ∧
    m ≤ r.2 ∧ r.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m → wVal r.1 inp r.2 = xor (wVal gs inp u) (wVal gs inp v) := by
  unfold mkXor
  set r1 := mkOr m gs u v with hr1
  have h1 := mkOr_spec hv hu hv'; dsimp only at h1; rw [← hr1] at h1
  rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
  set r2 := mkAnd m r1.1 u v with hr2
  have h2 := mkAnd_spec h1v (u := u) (v := v) (by omega) (by omega); dsimp only at h2; rw [← hr2] at h2
  rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
  set r3 := mkNot m r2.1 r2.2 with hr3
  have h3 := mkNot_spec h2v h2lt; dsimp only at h3; rw [← hr3] at h3
  rcases h3 with ⟨h3v, h3p, h3l, h3ge, h3lt, h3val⟩
  set r4 := mkAnd m r3.1 r1.2 r3.2 with hr4
  have h4 := mkAnd_spec h3v (u := r1.2) (v := r3.2) (by omega) h3lt; dsimp only at h4; rw [← hr4] at h4
  rcases h4 with ⟨h4v, h4p, h4l, h4ge, h4lt, h4val⟩
  refine ⟨h4v, h1p.trans (h2p.trans (h3p.trans h4p)), by omega, h4ge, h4lt, fun inp hinp => ?_⟩
  rw [h4val inp hinp, wVal_prefix (h2p.trans h3p) hinp h1lt,
      h1val inp hinp, h3val inp hinp, h2val inp hinp,
      wVal_prefix h1p hinp hu, wVal_prefix h1p hinp hv']
  cases wVal gs inp u <;> cases wVal gs inp v <;> decide

private def mkHalfAdder (m : ℕ) (gs : List Gate) (a c : ℕ) : List Gate × ℕ × ℕ :=
  let r1 := mkXor m gs a c
  let r2 := mkAnd m r1.1 a c
  (r2.1, r1.2, r2.2)

private lemma mkHalfAdder_spec {m : ℕ} {gs : List Gate} (hv : CValid m gs) {a c : ℕ}
    (ha : a < m + gs.length) (hc : c < m + gs.length) :
    let r := mkHalfAdder m gs a c
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 5 ∧
    r.2.1 < m + r.1.length ∧ r.2.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m →
      (wVal r.1 inp r.2.1).toNat + 2 * (wVal r.1 inp r.2.2).toNat =
        (wVal gs inp a).toNat + (wVal gs inp c).toNat := by
  unfold mkHalfAdder; dsimp only
  set r1 := mkXor m gs a c with hr1
  have h1 := mkXor_spec hv ha hc; dsimp only at h1; rw [← hr1] at h1
  rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
  set r2 := mkAnd m r1.1 a c with hr2
  have h2 := mkAnd_spec h1v (u := a) (v := c) (by omega) (by omega); dsimp only at h2; rw [← hr2] at h2
  rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
  refine ⟨h2v, h1p.trans h2p, by omega, by omega, h2lt, fun inp hinp => ?_⟩
  rw [wVal_prefix h2p hinp h1lt, h1val inp hinp,
      h2val inp hinp, wVal_prefix h1p hinp ha, wVal_prefix h1p hinp hc]
  cases wVal gs inp a <;> cases wVal gs inp c <;> decide

private def mkFullAdder (m : ℕ) (gs : List Gate) (a b c : ℕ) : List Gate × ℕ × ℕ :=
  let r1 := mkXor m gs a b
  let r2 := mkXor m r1.1 r1.2 c
  let r3 := mkAnd m r2.1 a b
  let r4 := mkAnd m r3.1 r1.2 c
  let r5 := mkOr m r4.1 r3.2 r4.2
  (r5.1, r2.2, r5.2)

private lemma mkFullAdder_spec {m : ℕ} {gs : List Gate} (hv : CValid m gs) {a b c : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    let r := mkFullAdder m gs a b c
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 11 ∧
    r.2.1 < m + r.1.length ∧ r.2.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m →
      (wVal r.1 inp r.2.1).toNat + 2 * (wVal r.1 inp r.2.2).toNat =
        (wVal gs inp a).toNat + (wVal gs inp b).toNat + (wVal gs inp c).toNat := by
  unfold mkFullAdder; dsimp only
  set r1 := mkXor m gs a b with hr1
  have h1 := mkXor_spec hv ha hb; dsimp only at h1; rw [← hr1] at h1
  rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
  set r2 := mkXor m r1.1 r1.2 c with hr2
  have h2 := mkXor_spec h1v (u := r1.2) (v := c) h1lt (by omega); dsimp only at h2; rw [← hr2] at h2
  rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
  set r3 := mkAnd m r2.1 a b with hr3
  have h3 := mkAnd_spec h2v (u := a) (v := b) (by omega) (by omega); dsimp only at h3; rw [← hr3] at h3
  rcases h3 with ⟨h3v, h3p, h3l, h3ge, h3lt, h3val⟩
  set r4 := mkAnd m r3.1 r1.2 c with hr4
  have h4 := mkAnd_spec h3v (u := r1.2) (v := c) (by omega) (by omega); dsimp only at h4; rw [← hr4] at h4
  rcases h4 with ⟨h4v, h4p, h4l, h4ge, h4lt, h4val⟩
  set r5 := mkOr m r4.1 r3.2 r4.2 with hr5
  have h5 := mkOr_spec h4v (u := r3.2) (v := r4.2) (by omega) h4lt; dsimp only at h5; rw [← hr5] at h5
  rcases h5 with ⟨h5v, h5p, h5l, h5ge, h5lt, h5val⟩
  refine ⟨h5v, h1p.trans (h2p.trans (h3p.trans (h4p.trans h5p))), by omega,
    by omega, h5lt, fun inp hinp => ?_⟩
  have hv1 := h1val inp hinp
  have hv2 : wVal r2.1 inp r2.2 = xor (xor (wVal gs inp a) (wVal gs inp b)) (wVal gs inp c) := by
    rw [h2val inp hinp, hv1, wVal_prefix h1p hinp hc]
  have hv3 : wVal r3.1 inp r3.2 = (wVal gs inp a && wVal gs inp b) := by
    rw [h3val inp hinp,
        wVal_prefix (h1p.trans h2p) hinp ha, wVal_prefix (h1p.trans h2p) hinp hb]
  have hv4 : wVal r4.1 inp r4.2 = (xor (wVal gs inp a) (wVal gs inp b) && wVal gs inp c) := by
    rw [h4val inp hinp,
        wVal_prefix (h2p.trans h3p) hinp h1lt, hv1,
        wVal_prefix (h1p.trans (h2p.trans h3p)) hinp hc]
  rw [wVal_prefix (h3p.trans (h4p.trans h5p)) hinp h2lt, hv2,
      h5val inp hinp, wVal_prefix h4p hinp h3lt, hv3, hv4]
  cases wVal gs inp a <;> cases wVal gs inp b <;> cases wVal gs inp c <;> decide

private def bitsVal (gs : List Gate) (inp : List Bool) : List ℕ → ℕ
  | [] => 0
  | w :: ws => (wVal gs inp w).toNat + 2 * bitsVal gs inp ws

private lemma bitsVal_lt (gs : List Gate) (inp : List Bool) (ws : List ℕ) :
    bitsVal gs inp ws < 2 ^ ws.length := by
  induction ws with
  | nil => simp [bitsVal]
  | cons w ws ih =>
    simp only [bitsVal, List.length_cons, pow_succ']
    have : (wVal gs inp w).toNat ≤ 1 := by cases wVal gs inp w <;> decide
    omega

private lemma bitsVal_prefix {m : ℕ} {gs1 gs2 : List Gate} (hp : gs1 <+: gs2)
    {inp : List Bool} (hinp : inp.length = m) {ws : List ℕ}
    (hws : ∀ w ∈ ws, w < m + gs1.length) :
    bitsVal gs2 inp ws = bitsVal gs1 inp ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [bitsVal]
    rw [wVal_prefix hp hinp (hws w (by simp)),
        ih (fun u hu => hws u (by simp [hu]))]

private lemma bitsVal_replicate_zero {m : ℕ} (hm : 2 ≤ m) (gs : List Gate)
    (inp : List Bool) (hinp : inp.length = m) (h0 : inp.getD 0 false = false) (k : ℕ) :
    bitsVal gs inp (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, bitsVal, wVal_input gs inp (by rw [hinp]; omega), h0, ih]
    rfl

private def mkInc (m : ℕ) : List Gate → List ℕ → ℕ → List Gate × List ℕ × ℕ
  | gs, [], cin => (gs, [], cin)
  | gs, b :: bs, cin =>
    let r1 := mkHalfAdder m gs b cin
    let r2 := mkInc m r1.1 bs r1.2.2
    (r2.1, r1.2.1 :: r2.2.1, r2.2.2)

private lemma mkInc_spec {m : ℕ} {gs : List Gate} (hv : CValid m gs) {bits : List ℕ}
    (hbs : ∀ w ∈ bits, w < m + gs.length) {cin : ℕ} (hcin : cin < m + gs.length) :
    let r := mkInc m gs bits cin
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 5 * bits.length ∧
    r.2.1.length = bits.length ∧ (∀ w ∈ r.2.1, w < m + r.1.length) ∧ r.2.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m →
      bitsVal r.1 inp r.2.1 + 2 ^ bits.length * (wVal r.1 inp r.2.2).toNat =
        bitsVal gs inp bits + (wVal gs inp cin).toNat := by
  induction bits generalizing gs cin with
  | nil =>
    refine ⟨hv, List.prefix_rfl, by simp [mkInc], rfl, fun _ h => by simp [mkInc] at h, hcin,
      fun inp _ => by simp [mkInc, bitsVal]⟩
  | cons b bs ih =>
    unfold mkInc; dsimp only
    set r1 := mkHalfAdder m gs b cin with hr1
    have h1 := mkHalfAdder_spec hv (hbs b (by simp)) hcin; dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨h1v, h1p, h1l, h1w1, h1w2, h1val⟩
    have hbs' : ∀ w ∈ bs, w < m + r1.1.length := fun w hw => by
      have := hbs w (by simp [hw]); omega
    set r2 := mkInc m r1.1 bs r1.2.2 with hr2
    have h2 := ih h1v hbs' h1w2; dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨h2v, h2p, h2l, h2bl, h2bw, h2c, h2val⟩
    refine ⟨h2v, h1p.trans h2p, by simp only [List.length_cons]; omega,
      by simp [h2bl], ?_, h2c, fun inp hinp => ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact h2bw w hw
    · simp only [bitsVal, List.length_cons, pow_succ']
      rw [wVal_prefix h2p hinp h1w1]
      have eq1 := h1val inp hinp
      have eq2 := h2val inp hinp
      rw [bitsVal_prefix h1p hinp (fun w hw => hbs w (by simp [hw]))] at eq2
      linarith

private def mkSumList (m w0 : ℕ) : List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, List.replicate w0 0)
  | gs, w :: ws =>
    let r1 := mkSumList m w0 gs ws
    let r2 := mkInc m r1.1 r1.2 w
    (r2.1, r2.2.1)

private lemma mkSumList_spec {m w0 : ℕ} (hm : 2 ≤ m) {gs : List Gate} (hv : CValid m gs)
    {ws : List ℕ} (hws : ∀ w ∈ ws, w < m + gs.length) (hw0 : ws.length < 2 ^ w0) :
    let r := mkSumList m w0 gs ws
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 5 * w0 * ws.length ∧
    r.2.length = w0 ∧ (∀ w ∈ r.2, w < m + r.1.length) ∧
    ∀ inp : List Bool, inp.length = m → inp.getD 0 false = false →
      bitsVal r.1 inp r.2 = ws.countP (fun w => wVal gs inp w) := by
  induction ws generalizing gs with
  | nil =>
    refine ⟨hv, List.prefix_rfl, by simp [mkSumList], by simp [mkSumList],
      fun w hw => by simp [mkSumList] at hw; omega,
      fun inp hinp h0 => by simp [mkSumList, bitsVal_replicate_zero hm gs inp hinp h0]⟩
  | cons w ws ih =>
    unfold mkSumList; dsimp only
    have hws_sub : ∀ u ∈ ws, u < m + gs.length := fun u hu => hws u (by simp [hu])
    have hw0_sub : ws.length < 2 ^ w0 := by simp at hw0; omega
    set r1 := mkSumList m w0 gs ws with hr1
    have h1 := ih hv hws_sub hw0_sub; dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨h1v, h1p, h1l, h1bl, h1bw, h1val⟩
    have hw_lt : w < m + r1.1.length := by have := hws w (by simp); omega
    set r2 := mkInc m r1.1 r1.2 w with hr2
    have h2 := mkInc_spec h1v h1bw hw_lt; dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨h2v, h2p, h2l, h2bl, h2bw, h2c, h2val⟩
    refine ⟨h2v, h1p.trans h2p, ?_, by rw [h2bl, h1bl], h2bw,
      fun inp hinp h0 => ?_⟩
    · simp only [List.length_cons]
      rw [h2l, h1bl, h1l]
      ring
    · have eq2 := h2val inp hinp
      rw [h1val inp hinp h0, wVal_prefix h1p hinp (hws w (by simp)), h1bl] at eq2
      have hcnt : ws.countP (fun u => wVal gs inp u) ≤ ws.length := List.countP_le_length
      have hwb : (wVal gs inp w).toNat ≤ 1 := by cases wVal gs inp w <;> decide
      have hcout : (wVal r2.1 inp r2.2.2).toNat = 0 := by
        by_contra hne
        have hpos : 1 ≤ (wVal r2.1 inp r2.2.2).toNat := by omega
        have hge : 2 ^ w0 ≤ 2 ^ w0 * (wVal r2.1 inp r2.2.2).toNat :=
          Nat.le_mul_of_pos_right _ (by omega)
        simp only [List.length_cons] at hw0
        omega
      rw [hcout, mul_zero, add_zero] at eq2
      rw [eq2]
      simp only [List.countP_cons]
      cases wVal gs inp w <;> simp

private def mkAddAux (m : ℕ) : List Gate → ℕ → List ℕ → List ℕ → ℕ → List Gate × List ℕ
  | gs, 0, _, _, cin => (gs, [cin])
  | gs, k + 1, as, bs, cin =>
    let a := as.headD 0
    let b := bs.headD 0
    let r1 := mkFullAdder m gs a b cin
    let r2 := mkAddAux m r1.1 k as.tail bs.tail r1.2.2
    (r2.1, r1.2.1 :: r2.2)

private lemma mkAddAux_spec {m : ℕ} (hm : 2 ≤ m) {gs : List Gate} (hv : CValid m gs)
    {k : ℕ} {as bs : List ℕ} (has_len : as.length ≤ k) (hbs_len : bs.length ≤ k)
    (has : ∀ w ∈ as, w < m + gs.length) (hbs : ∀ w ∈ bs, w < m + gs.length)
    {cin : ℕ} (hcin : cin < m + gs.length) :
    let r := mkAddAux m gs k as bs cin
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 11 * k ∧
    r.2.length = k + 1 ∧ (∀ w ∈ r.2, w < m + r.1.length) ∧
    ∀ inp : List Bool, inp.length = m → inp.getD 0 false = false →
      bitsVal r.1 inp r.2 = bitsVal gs inp as + bitsVal gs inp bs + (wVal gs inp cin).toNat := by
  induction k generalizing gs as bs cin with
  | zero =>
    have ha0 : as = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hb0 : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ha0; subst hb0
    refine ⟨hv, List.prefix_rfl, by simp [mkAddAux], rfl,
      fun w hw => by simp [mkAddAux] at hw; subst hw; exact hcin,
      fun inp _ _ => by simp [mkAddAux, bitsVal]⟩
  | succ k ih =>
    unfold mkAddAux; dsimp only
    have ha_lt : as.headD 0 < m + gs.length := by
      cases as with
      | nil => simp; omega
      | cons a atail => exact has a (by simp)
    have hb_lt : bs.headD 0 < m + gs.length := by
      cases bs with
      | nil => simp; omega
      | cons b btail => exact hbs b (by simp)
    set r1 := mkFullAdder m gs (as.headD 0) (bs.headD 0) cin with hr1
    have h1 := mkFullAdder_spec hv ha_lt hb_lt hcin; dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨h1v, h1p, h1l, h1w1, h1w2, h1val⟩
    have hat_len : as.tail.length ≤ k := by cases as <;> simp at has_len ⊢ <;> omega
    have hbt_len : bs.tail.length ≤ k := by cases bs <;> simp at hbs_len ⊢ <;> omega
    have hat : ∀ w ∈ as.tail, w < m + r1.1.length := fun w hw => by
      have : w ∈ as := List.mem_of_mem_tail hw
      have := has w this; omega
    have hbt : ∀ w ∈ bs.tail, w < m + r1.1.length := fun w hw => by
      have : w ∈ bs := List.mem_of_mem_tail hw
      have := hbs w this; omega
    set r2 := mkAddAux m r1.1 k as.tail bs.tail r1.2.2 with hr2
    have h2 := ih h1v hat_len hbt_len hat hbt h1w2; dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨h2v, h2p, h2l, h2bl, h2bw, h2val⟩
    refine ⟨h2v, h1p.trans h2p, by omega, by simp [h2bl], ?_,
      fun inp hinp h0 => ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact h2bw w hw
    · simp only [bitsVal]
      rw [wVal_prefix h2p hinp h1w1, h2val inp hinp h0]
      have eq1 := h1val inp hinp
      have hpa : bitsVal r1.1 inp as.tail = bitsVal gs inp as.tail :=
        bitsVal_prefix h1p hinp (fun w hw => has w (List.mem_of_mem_tail hw))
      have hpb : bitsVal r1.1 inp bs.tail = bitsVal gs inp bs.tail :=
        bitsVal_prefix h1p hinp (fun w hw => hbs w (List.mem_of_mem_tail hw))
      rw [hpa, hpb]
      have ha_eq : (wVal gs inp (as.headD 0)).toNat + 2 * bitsVal gs inp as.tail = bitsVal gs inp as := by
        cases as with
        | nil =>
          simp only [List.headD_nil, List.tail_nil, bitsVal]
          rw [wVal_input gs inp (by rw [hinp]; omega), h0]; rfl
        | cons a atail => simp [bitsVal]
      have hb_eq : (wVal gs inp (bs.headD 0)).toNat + 2 * bitsVal gs inp bs.tail = bitsVal gs inp bs := by
        cases bs with
        | nil =>
          simp only [List.headD_nil, List.tail_nil, bitsVal]
          rw [wVal_input gs inp (by rw [hinp]; omega), h0]; rfl
        | cons b btail => simp [bitsVal]
      omega

private def mkAddBits (m : ℕ) (gs : List Gate) (k : ℕ) (as bs : List ℕ) : List Gate × List ℕ :=
  mkAddAux m gs k as bs 0

private lemma mkAddBits_spec {m : ℕ} (hm : 2 ≤ m) {gs : List Gate} (hv : CValid m gs)
    {k : ℕ} {as bs : List ℕ} (has_len : as.length ≤ k) (hbs_len : bs.length ≤ k)
    (has : ∀ w ∈ as, w < m + gs.length) (hbs : ∀ w ∈ bs, w < m + gs.length) :
    let r := mkAddBits m gs k as bs
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 11 * k ∧
    r.2.length = k + 1 ∧ (∀ w ∈ r.2, w < m + r.1.length) ∧
    ∀ inp : List Bool, inp.length = m → inp.getD 0 false = false →
      bitsVal r.1 inp r.2 = bitsVal gs inp as + bitsVal gs inp bs := by
  unfold mkAddBits
  obtain ⟨hv1, hp1, hl1, hbl1, hbw1, hval1⟩ := mkAddAux_spec hm hv has_len hbs_len has hbs (cin := 0) (by omega)
  refine ⟨hv1, hp1, hl1, hbl1, hbw1, fun inp hinp h0 => ?_⟩
  rw [hval1 inp hinp h0, wVal_input gs inp (w := 0) (by rw [hinp]; omega), h0]
  simp

private def mkLtList (m : ℕ) : List Gate → List ℕ → ℕ → ℕ → List Gate × ℕ
  | gs, [], _, acc => (gs, acc)
  | gs, w :: ws, K, acc =>
    let r1 := mkNot m gs w
    let r2 := if K % 2 = 1 then mkOr m r1.1 r1.2 acc else mkAnd m r1.1 r1.2 acc
    mkLtList m r2.1 ws (K / 2) r2.2

private lemma mkLtList_spec {m : ℕ} {gs : List Gate} (hv : CValid m gs) {ws : List ℕ}
    (hws : ∀ w ∈ ws, w < m + gs.length) {K acc : ℕ} (hK : K < 2 ^ ws.length)
    (hacc_ge : m ≤ acc) (hacc_lt : acc < m + gs.length) :
    let r := mkLtList m gs ws K acc
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + 2 * ws.length ∧
    m ≤ r.2 ∧ r.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m →
      wVal r.1 inp r.2 = decide (bitsVal gs inp ws < K ∨ (bitsVal gs inp ws = K ∧ wVal gs inp acc = true)) := by
  induction ws generalizing gs K acc with
  | nil =>
    have hK0 : K = 0 := by simp at hK; omega
    subst hK0
    refine ⟨hv, List.prefix_rfl, by simp [mkLtList], hacc_ge, hacc_lt,
      fun inp _ => by simp [mkLtList, bitsVal]⟩
  | cons w ws ih =>
    unfold mkLtList; dsimp only
    set r1 := mkNot m gs w with hr1
    have h1 := mkNot_spec hv (hws w (by simp)); dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
    have hK' : K / 2 < 2 ^ ws.length := by
      simp only [List.length_cons, pow_succ'] at hK; omega
    by_cases hodd : K % 2 = 1
    · simp only [hodd, ↓reduceIte]
      set r2 := mkOr m r1.1 r1.2 acc with hr2
      have h2 := mkOr_spec h1v (u := r1.2) (v := acc) h1lt (by omega); dsimp only at h2; rw [← hr2] at h2
      rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
      have hws' : ∀ u ∈ ws, u < m + r2.1.length := fun u hu => by
        have := hws u (by simp [hu]); omega
      set r3 := mkLtList m r2.1 ws (K / 2) r2.2 with hr3
      have h3 := ih h2v hws' hK' h2ge h2lt; dsimp only at h3; rw [← hr3] at h3
      rcases h3 with ⟨h3v, h3p, h3l, h3ge, h3lt, h3val⟩
      refine ⟨h3v, h1p.trans (h2p.trans h3p), by simp only [List.length_cons]; omega,
        h3ge, h3lt, fun inp hinp => ?_⟩
      rw [h3val inp hinp,
          bitsVal_prefix (h1p.trans h2p) hinp (fun u hu => hws u (by simp [hu])),
          h2val inp hinp, h1val inp hinp, wVal_prefix h1p hinp hacc_lt]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      simp only [Bool.or_eq_true, Bool.not_eq_true', bitsVal]
      cases wVal gs inp w <;> cases wVal gs inp acc <;> simp <;> omega
    · simp only [hodd, ↓reduceIte]
      set r2 := mkAnd m r1.1 r1.2 acc with hr2
      have h2 := mkAnd_spec h1v (u := r1.2) (v := acc) h1lt (by omega); dsimp only at h2; rw [← hr2] at h2
      rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
      have hws' : ∀ u ∈ ws, u < m + r2.1.length := fun u hu => by
        have := hws u (by simp [hu]); omega
      set r3 := mkLtList m r2.1 ws (K / 2) r2.2 with hr3
      have h3 := ih h2v hws' hK' h2ge h2lt; dsimp only at h3; rw [← hr3] at h3
      rcases h3 with ⟨h3v, h3p, h3l, h3ge, h3lt, h3val⟩
      refine ⟨h3v, h1p.trans (h2p.trans h3p), by simp only [List.length_cons]; omega,
        h3ge, h3lt, fun inp hinp => ?_⟩
      rw [h3val inp hinp,
          bitsVal_prefix (h1p.trans h2p) hinp (fun u hu => hws u (by simp [hu])),
          h2val inp hinp, h1val inp hinp, wVal_prefix h1p hinp hacc_lt]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      simp only [Bool.and_eq_true, Bool.not_eq_true', bitsVal]
      cases wVal gs inp w <;> cases wVal gs inp acc <;> simp <;> omega

private def mkLtConst (m : ℕ) (gs : List Gate) (ws : List ℕ) (K : ℕ) : List Gate × ℕ :=
  let r0 := mkFalse m gs
  mkLtList m r0.1 ws K r0.2

private lemma mkLtConst_spec {m : ℕ} (hm : 2 ≤ m) {gs : List Gate} (hv : CValid m gs)
    {ws : List ℕ} (hws : ∀ w ∈ ws, w < m + gs.length) {K : ℕ} (hK : K < 2 ^ ws.length) :
    let r := mkLtConst m gs ws K
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + (1 + 2 * ws.length) ∧
    m ≤ r.2 ∧ r.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m → inp.getD 0 false = false →
      wVal r.1 inp r.2 = decide (bitsVal gs inp ws < K) := by
  unfold mkLtConst; dsimp only
  set r0 := mkFalse m gs with hr0
  have h0 := mkFalse_spec hm hv; dsimp only at h0; rw [← hr0] at h0
  rcases h0 with ⟨h0v, h0p, h0l, h0ge, h0lt, h0val⟩
  have hws' : ∀ w ∈ ws, w < m + r0.1.length := fun w hw => by have := hws w hw; omega
  set r1 := mkLtList m r0.1 ws K r0.2 with hr1
  have h1 := mkLtList_spec h0v hws' hK h0ge h0lt; dsimp only at h1; rw [← hr1] at h1
  rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
  refine ⟨h1v, h0p.trans h1p, by omega, h1ge, h1lt,
    fun inp hinp h0i => ?_⟩
  rw [h1val inp hinp, bitsVal_prefix h0p hinp hws, h0val inp hinp h0i]
  simp

private def mkGtList (m : ℕ) : List Gate → List ℕ → ℕ → ℕ → List Gate × ℕ
  | gs, [], _, acc => (gs, acc)
  | gs, w :: ws, K, acc =>
    let r1 := if K % 2 = 1 then mkAnd m gs w acc else mkOr m gs w acc
    mkGtList m r1.1 ws (K / 2) r1.2

private lemma mkGtList_spec {m : ℕ} {gs : List Gate} (hv : CValid m gs) {ws : List ℕ}
    (hws : ∀ w ∈ ws, w < m + gs.length) {K acc : ℕ} (hK : K < 2 ^ ws.length)
    (hacc_ge : m ≤ acc) (hacc_lt : acc < m + gs.length) :
    let r := mkGtList m gs ws K acc
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + ws.length ∧
    m ≤ r.2 ∧ r.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m →
      wVal r.1 inp r.2 = decide (K < bitsVal gs inp ws ∨ (K = bitsVal gs inp ws ∧ wVal gs inp acc = true)) := by
  induction ws generalizing gs K acc with
  | nil =>
    have hK0 : K = 0 := by simp at hK; omega
    subst hK0
    refine ⟨hv, List.prefix_rfl, by simp [mkGtList], hacc_ge, hacc_lt,
      fun inp _ => by simp [mkGtList, bitsVal]⟩
  | cons w ws ih =>
    unfold mkGtList; dsimp only
    have hK' : K / 2 < 2 ^ ws.length := by
      simp only [List.length_cons, pow_succ'] at hK; omega
    by_cases hodd : K % 2 = 1
    · simp only [hodd, ↓reduceIte]
      set r1 := mkAnd m gs w acc with hr1
      have h1 := mkAnd_spec hv (hws w (by simp)) hacc_lt; dsimp only at h1; rw [← hr1] at h1
      rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
      have hws' : ∀ u ∈ ws, u < m + r1.1.length := fun u hu => by
        have := hws u (by simp [hu]); omega
      set r2 := mkGtList m r1.1 ws (K / 2) r1.2 with hr2
      have h2 := ih h1v hws' hK' h1ge h1lt; dsimp only at h2; rw [← hr2] at h2
      rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
      refine ⟨h2v, h1p.trans h2p, by simp only [List.length_cons]; omega,
        h2ge, h2lt, fun inp hinp => ?_⟩
      rw [h2val inp hinp,
          bitsVal_prefix h1p hinp (fun u hu => hws u (by simp [hu])),
          h1val inp hinp]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      simp only [Bool.and_eq_true, bitsVal]
      cases wVal gs inp w <;> cases wVal gs inp acc <;> simp <;> omega
    · simp only [hodd, ↓reduceIte]
      set r1 := mkOr m gs w acc with hr1
      have h1 := mkOr_spec hv (hws w (by simp)) hacc_lt; dsimp only at h1; rw [← hr1] at h1
      rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
      have hws' : ∀ u ∈ ws, u < m + r1.1.length := fun u hu => by
        have := hws u (by simp [hu]); omega
      set r2 := mkGtList m r1.1 ws (K / 2) r1.2 with hr2
      have h2 := ih h1v hws' hK' h1ge h1lt; dsimp only at h2; rw [← hr2] at h2
      rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
      refine ⟨h2v, h1p.trans h2p, by simp only [List.length_cons]; omega,
        h2ge, h2lt, fun inp hinp => ?_⟩
      rw [h2val inp hinp,
          bitsVal_prefix h1p hinp (fun u hu => hws u (by simp [hu])),
          h1val inp hinp]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      simp only [Bool.or_eq_true, bitsVal]
      cases wVal gs inp w <;> cases wVal gs inp acc <;> simp <;> omega

private def mkGtConst (m : ℕ) (gs : List Gate) (ws : List ℕ) (K : ℕ) : List Gate × ℕ :=
  let r0 := mkFalse m gs
  mkGtList m r0.1 ws K r0.2

private lemma mkGtConst_spec {m : ℕ} (hm : 2 ≤ m) {gs : List Gate} (hv : CValid m gs)
    {ws : List ℕ} (hws : ∀ w ∈ ws, w < m + gs.length) {K : ℕ} (hK : K < 2 ^ ws.length) :
    let r := mkGtConst m gs ws K
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + (1 + ws.length) ∧
    m ≤ r.2 ∧ r.2 < m + r.1.length ∧
    ∀ inp : List Bool, inp.length = m → inp.getD 0 false = false →
      wVal r.1 inp r.2 = decide (K < bitsVal gs inp ws) := by
  unfold mkGtConst; dsimp only
  set r0 := mkFalse m gs with hr0
  have h0 := mkFalse_spec hm hv; dsimp only at h0; rw [← hr0] at h0
  rcases h0 with ⟨h0v, h0p, h0l, h0ge, h0lt, h0val⟩
  have hws' : ∀ w ∈ ws, w < m + r0.1.length := fun w hw => by have := hws w hw; omega
  set r1 := mkGtList m r0.1 ws K r0.2 with hr1
  have h1 := mkGtList_spec h0v hws' hK h0ge h0lt; dsimp only at h1; rw [← hr1] at h1
  rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
  refine ⟨h1v, h0p.trans h1p, by omega, h1ge, h1lt,
    fun inp hinp h0i => ?_⟩
  rw [h1val inp hinp, bitsVal_prefix h0p hinp hws, h0val inp hinp h0i]
  simp

private def mkHoleFlags (m : ℕ) : List Gate → List ℕ → List Gate × List ℕ × List ℕ
  | gs, [] =>
    let r1 := mkFalse m gs
    let r2 := mkFalse m r1.1
    (r2.1, [r1.2], [r2.2])
  | gs, w :: ws =>
    let r0 := mkHoleFlags m gs ws
    let sLast := r0.2.1.headD 0
    let tLast := r0.2.2.headD 0
    let rs := mkOr m r0.1 sLast w
    let rp := mkAnd m rs.1 sLast w
    let rt := mkOr m rp.1 tLast rp.2
    (rt.1, rs.2 :: r0.2.1, rt.2 :: r0.2.2)

private lemma mkHoleFlags_spec {m : ℕ} (hm : 2 ≤ m) {gs : List Gate} (hv : CValid m gs)
    {ws : List ℕ} (hws : ∀ w ∈ ws, w < m + gs.length) :
    let r := mkHoleFlags m gs ws
    CValid m r.1 ∧ gs <+: r.1 ∧ r.1.length = gs.length + (2 + 3 * ws.length) ∧
    r.2.1.length = ws.length + 1 ∧ r.2.2.length = ws.length + 1 ∧
    (∀ u ∈ r.2.1, m ≤ u ∧ u < m + r.1.length) ∧
    (∀ u ∈ r.2.2, m ≤ u ∧ u < m + r.1.length) ∧
    r.2.1.Nodup ∧ r.2.2.Nodup ∧ (∀ u ∈ r.2.1, u ∉ r.2.2) ∧
    (∀ u ∈ r.2.1, m + gs.length ≤ u) ∧ (∀ u ∈ r.2.2, m + gs.length ≤ u) ∧
    ∀ inp : List Bool, inp.length = m → inp.getD 0 false = false →
      wVal r.1 inp (r.2.1.headD 0) = decide (1 ≤ ws.countP (fun w => wVal gs inp w)) ∧
      wVal r.1 inp (r.2.2.headD 0) = decide (2 ≤ ws.countP (fun w => wVal gs inp w)) := by
  induction ws generalizing gs with
  | nil =>
    unfold mkHoleFlags; dsimp only
    set r1 := mkFalse m gs with hr1
    have h1 := mkFalse_spec hm hv; dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
    set r2 := mkFalse m r1.1 with hr2
    have h2 := mkFalse_spec hm h1v; dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
    have hr1w : r1.2 = m + gs.length := by rw [hr1]; rfl
    have hr2w : r2.2 = m + r1.1.length := by rw [hr2]; rfl
    refine ⟨h2v, h1p.trans h2p, by simp only [List.length_nil]; omega, rfl, rfl,
      fun u hu => by simp at hu; subst hu; omega,
      fun u hu => by simp at hu; subst hu; omega,
      by simp, by simp, fun u hu h2u => by simp at hu h2u; omega,
      fun u hu => by simp at hu; omega,
      fun u hu => by simp at hu; omega,
      fun inp hinp h0 => ?_⟩
    simp only [List.headD_cons, List.countP_nil]
    rw [wVal_prefix h2p hinp h1lt, h1val inp hinp h0, h2val inp hinp h0]
    simp
  | cons w ws ih =>
    unfold mkHoleFlags; dsimp only
    set r0 := mkHoleFlags m gs ws with hr0
    have h0 := ih hv (fun u hu => hws u (by simp [hu])); dsimp only at h0; rw [← hr0] at h0
    rcases h0 with ⟨h0v, h0p, h0l, h0sl, h0tl, h0sb, h0tb, h0snd, h0tnd, h0disj, h0sge, h0tge, h0val⟩
    have hs_mem : r0.2.1.headD 0 ∈ r0.2.1 := by
      cases h : r0.2.1 with
      | nil => rw [h] at h0sl; simp at h0sl
      | cons x xs => simp
    have ht_mem : r0.2.2.headD 0 ∈ r0.2.2 := by
      cases h : r0.2.2 with
      | nil => rw [h] at h0tl; simp at h0tl
      | cons x xs => simp
    have hs_lt := (h0sb _ hs_mem).2
    have ht_lt := (h0tb _ ht_mem).2
    have hw_lt : w < m + r0.1.length := by have := hws w (by simp); omega
    set rs := mkOr m r0.1 (r0.2.1.headD 0) w with hrs
    have hrs_h := mkOr_spec h0v hs_lt hw_lt; dsimp only at hrs_h; rw [← hrs] at hrs_h
    rcases hrs_h with ⟨hrsv, hrsp, hrsl, hrsge, hrslt, hrsval⟩
    set rp := mkAnd m rs.1 (r0.2.1.headD 0) w with hrp
    have hrp_h := mkAnd_spec hrsv (u := r0.2.1.headD 0) (v := w) (by omega) (by omega); dsimp only at hrp_h; rw [← hrp] at hrp_h
    rcases hrp_h with ⟨hrpv, hrpp, hrpl, hrpge, hrplt, hrpval⟩
    set rt := mkOr m rp.1 (r0.2.2.headD 0) rp.2 with hrt
    have hrt_h := mkOr_spec hrpv (u := r0.2.2.headD 0) (v := rp.2) (by omega) hrplt; dsimp only at hrt_h; rw [← hrt] at hrt_h
    rcases hrt_h with ⟨hrtv, hrtp, hrtl, hrtge, hrtlt, hrtval⟩
    have hrs_w : rs.2 = m + r0.1.length := by rw [hrs]; rfl
    have hrp_w : rp.2 = m + rs.1.length := by rw [hrp]; rfl
    have hrt_w : rt.2 = m + rp.1.length := by rw [hrt]; rfl
    refine ⟨hrtv, h0p.trans (hrsp.trans (hrpp.trans hrtp)),
      by simp only [List.length_cons]; omega,
      by simp [h0sl], by simp [h0tl],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun inp hinp h0i => ?_⟩
    · intro u hu; simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · omega
      · have := h0sb u hu; omega
    · intro u hu; simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · omega
      · have := h0tb u hu; omega
    · rw [List.nodup_cons]
      refine ⟨fun hmem => ?_, h0snd⟩
      have := (h0sb _ hmem).2; omega
    · rw [List.nodup_cons]
      refine ⟨fun hmem => ?_, h0tnd⟩
      have := (h0tb _ hmem).2; omega
    · intro u hu h2u
      simp only [List.mem_cons] at hu h2u
      rcases hu with rfl | hu
      · rcases h2u with heq | h2u
        · omega
        · have := (h0tb _ h2u).2; omega
      · rcases h2u with rfl | h2u
        · have := (h0sb _ hu).2; omega
        · exact h0disj u hu h2u
    · intro u hu; simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · omega
      · exact h0sge u hu
    · intro u hu; simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · omega
      · exact h0tge u hu
    · simp only [List.headD_cons, List.countP_cons]
      have hprev := h0val inp hinp h0i
      have hvw : wVal r0.1 inp w = wVal gs inp w :=
        wVal_prefix h0p hinp (hws w (by simp))
      have hv_rs : wVal rs.1 inp rs.2 = (wVal r0.1 inp (r0.2.1.headD 0) || wVal gs inp w) := by
        rw [hrsval inp hinp, hvw]
      have hv_rp : wVal rp.1 inp rp.2 = (wVal r0.1 inp (r0.2.1.headD 0) && wVal gs inp w) := by
        rw [hrpval inp hinp, wVal_prefix hrsp hinp hs_lt,
            wVal_prefix hrsp hinp hw_lt, hvw]
      have hv_rt : wVal rt.1 inp rt.2 =
          (wVal r0.1 inp (r0.2.2.headD 0) || (wVal r0.1 inp (r0.2.1.headD 0) && wVal gs inp w)) := by
        rw [hrtval inp hinp,
            wVal_prefix (hrsp.trans hrpp) hinp ht_lt, hv_rp]
      rw [wVal_prefix (hrpp.trans hrtp) hinp hrslt, hv_rs, hv_rt, hprev.1, hprev.2]
      cases wVal gs inp w
      · simp
      · constructor
        · rw [Bool.or_true]; symm; exact decide_eq_true (by simp)
        · rw [Bool.eq_iff_iff]; simp only [↓reduceIte, Bool.or_eq_true, Bool.and_true, decide_eq_true_eq]; omega

private inductive BTree (α : Type) where
  | leaf (x : α)
  | node (l r : BTree α)

private def BTree.size {α : Type} : BTree α → ℕ
  | .leaf _ => 1
  | .node l r => l.size + r.size

private def BTree.height {α : Type} : BTree α → ℕ
  | .leaf _ => 0
  | .node l r => max l.height r.height + 1

private def BTree.sumHeight {α : Type} : BTree α → ℕ
  | .leaf _ => 0
  | .node l r => l.sumHeight + r.sumHeight + (max l.height r.height + 1)

private def BTree.leaves {α : Type} : BTree α → List α
  | .leaf x => [x]
  | .node l r => l.leaves ++ r.leaves

private lemma BTree.leaves_length {α : Type} (t : BTree α) : t.leaves.length = t.size := by
  induction t with
  | leaf _ => rfl
  | node l r ihl ihr => simp [BTree.leaves, BTree.size, ihl, ihr]

private lemma BTree.size_pos {α : Type} (t : BTree α) : 0 < t.size := by
  induction t with
  | leaf _ => simp [BTree.size]
  | node l r ihl ihr => simp [BTree.size]; omega

private def mkBalanced {α : Type} : (xs : List α) → xs ≠ [] → BTree α
  | [x], _ => .leaf x
  | x :: y :: rest, _ =>
    let xs := x :: y :: rest
    let k := xs.length / 2
    have hlt1 : (xs.take k).length < xs.length := by
      simp [xs, k]; omega
    have hlt2 : (xs.drop k).length < xs.length := by
      simp [xs, k]; omega
    have hne1 : xs.take k ≠ [] := by
      intro h; have := congrArg List.length h; simp [xs, k] at this
    have hne2 : xs.drop k ≠ [] := by
      intro h; have := congrArg List.length h; simp [xs, k] at this; omega
    .node (mkBalanced (xs.take k) hne1) (mkBalanced (xs.drop k) hne2)
termination_by xs => xs.length

private lemma mkBalanced_leaves {α : Type} (xs : List α) (hne : xs ≠ []) :
    (mkBalanced xs hne).leaves = xs := by
  match xs with
  | [x] => simp [mkBalanced, BTree.leaves]
  | x :: y :: rest =>
    unfold mkBalanced
    dsimp only [BTree.leaves]
    set all := x :: y :: rest
    set k := all.length / 2
    have hlt1 : (all.take k).length < all.length := by simp [all, k]; omega
    have hlt2 : (all.drop k).length < all.length := by simp [all, k]; omega
    have hne1 : all.take k ≠ [] := by
      intro h; have := congrArg List.length h; simp [all, k] at this
    have hne2 : all.drop k ≠ [] := by
      intro h; have := congrArg List.length h; simp [all, k] at this; omega
    rw [mkBalanced_leaves (all.take k) hne1, mkBalanced_leaves (all.drop k) hne2,
        List.take_append_drop]
termination_by xs.length

private lemma mkBalanced_size {α : Type} (xs : List α) (hne : xs ≠ []) :
    (mkBalanced xs hne).size = xs.length := by
  rw [← BTree.leaves_length, mkBalanced_leaves]

private def balHeight : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => max (balHeight ((n + 2) / 2)) (balHeight ((n + 2) - (n + 2) / 2)) + 1

private lemma balHeight_mono : ∀ m1 m2 : ℕ, 1 ≤ m1 → m1 ≤ m2 → balHeight m1 ≤ balHeight m2 := by
  intro m1 m2 h1 hle
  induction m2 using Nat.strong_induction_on generalizing m1 with
  | ind m2 ih =>
    match m2 with
    | 0 => omega
    | 1 =>
      have : m1 = 1 := by omega
      subst this; exact le_rfl
    | k + 2 =>
      match m1 with
      | 0 => omega
      | 1 => simp [balHeight]
      | j + 2 =>
        simp only [balHeight]
        have h1' : (j + 2) / 2 ≤ (k + 2) / 2 := Nat.div_le_div_right hle
        have h2' : (j + 2) - (j + 2) / 2 ≤ (k + 2) - (k + 2) / 2 := by omega
        have ha := ih ((k + 2) / 2) (by omega) ((j + 2) / 2) (by omega) h1'
        have hb := ih ((k + 2) - (k + 2) / 2) (by omega) ((j + 2) - (j + 2) / 2) (by omega) h2'
        omega

private lemma balHeight_double (m : ℕ) (hm : 1 ≤ m) :
    balHeight (2 * m) = balHeight m + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 2 := ⟨2 * m - 2, by omega⟩
  rw [hk]
  have hdiv : (k + 2) / 2 = m := by omega
  have hsub : k + 2 - m = m := by omega
  conv_lhs => unfold balHeight
  rw [hdiv, hsub, max_self]

private lemma mkBalanced_height {α : Type} (xs : List α) (hne : xs ≠ []) :
    (mkBalanced xs hne).height = balHeight xs.length := by
  match xs with
  | [x] => simp [mkBalanced, BTree.height, balHeight]
  | x :: y :: rest =>
    unfold mkBalanced
    dsimp only [BTree.height]
    set all := x :: y :: rest
    set k := all.length / 2
    have hlt1 : (all.take k).length < all.length := by simp [all, k]; omega
    have hlt2 : (all.drop k).length < all.length := by simp [all, k]; omega
    have hne1 : all.take k ≠ [] := by
      intro h; have := congrArg List.length h; simp [all, k] at this
    have hne2 : all.drop k ≠ [] := by
      intro h; have := congrArg List.length h; simp [all, k] at this; omega
    rw [mkBalanced_height (all.take k) hne1, mkBalanced_height (all.drop k) hne2]
    have hl1 : (all.take k).length = all.length / 2 := by simp [all, k]; omega
    have hl2 : (all.drop k).length = all.length - all.length / 2 := by simp [all, k]
    rw [hl1, hl2]
    have hall : all.length = rest.length + 2 := by simp [all]
    rw [hall]
    simp [balHeight]
termination_by xs.length

private lemma mkBalanced_sumHeight {α : Type} (xs : List α) (hne : xs ≠ []) :
    (mkBalanced xs hne).sumHeight + 2 * (mkBalanced xs hne).height ≤ 4 * xs.length - 4 := by
  match xs with
  | [x] => simp [mkBalanced, BTree.sumHeight, BTree.height]
  | x :: y :: rest =>
    unfold mkBalanced
    dsimp only [BTree.sumHeight, BTree.height]
    set all := x :: y :: rest
    set k := all.length / 2
    generalize_proofs hne1 hne2
    have hlt1 : (all.take k).length < all.length := by simp [all, k]; omega
    have hlt2 : (all.drop k).length < all.length := by simp [all, k]; omega
    have ih1 := mkBalanced_sumHeight (all.take k) hne1
    have ih2 := mkBalanced_sumHeight (all.drop k) hne2
    have hl1 : (all.take k).length = k := by simp [all, k]; omega
    have hl2 : (all.drop k).length = all.length - k := by simp [all, k]
    have hht1 : (mkBalanced (all.take k) hne1).height = balHeight k := by
      rw [mkBalanced_height, hl1]
    have hht2 : (mkBalanced (all.drop k) hne2).height = balHeight (all.length - k) := by
      rw [mkBalanced_height, hl2]
    have hk1 : 1 ≤ k := by simp [all, k]; omega
    have hle1 : k ≤ all.length - k := by simp [all, k]; omega
    have hle2 : all.length - k ≤ 2 * k := by simp [all, k]; omega
    have hmono1 : balHeight k ≤ balHeight (all.length - k) := balHeight_mono _ _ hk1 hle1
    have hmono2 : balHeight (all.length - k) ≤ balHeight k + 1 := by
      rw [← balHeight_double k hk1]
      exact balHeight_mono _ _ (by omega) hle2
    rw [hht1] at ih1 ⊢
    rw [hht2] at ih2 ⊢
    rw [hl1] at ih1
    rw [hl2] at ih2
    have hmax : max (balHeight k) (balHeight (all.length - k)) = balHeight (all.length - k) :=
      max_eq_right hmono1
    rw [hmax]
    have hall_len : 2 ≤ all.length := by simp [all]
    change (mkBalanced (all.take k) hne1).sumHeight + (mkBalanced (all.drop k) hne2).sumHeight +
      (balHeight (all.length - k) + 1) + 2 * (balHeight (all.length - k) + 1) ≤ 4 * all.length - 4
    omega
termination_by xs.length

private lemma BTree.size_le_pow_height {α : Type} (t : BTree α) : t.size ≤ 2 ^ t.height := by
  induction t with
  | leaf _ => simp [BTree.size, BTree.height]
  | node l r ihl ihr =>
    simp only [BTree.size, BTree.height, pow_succ']
    have h1 : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h2 : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    omega

noncomputable section

private def inpVec {V : Type} [Fintype V] (x : V → Bool) : List Bool :=
  [false, true] ++ List.ofFn (fun j : Fin (Fintype.card V) => x ((Fintype.equivFin V).symm j))

private lemma inpVec_length {V : Type} [Fintype V] (x : V → Bool) :
    (inpVec x).length = 2 + Fintype.card V := by
  simp [inpVec]; omega

private lemma inpVec_zero {V : Type} [Fintype V] (x : V → Bool) :
    (inpVec x).getD 0 false = false := by
  simp [inpVec]

private lemma inpVec_one {V : Type} [Fintype V] (x : V → Bool) :
    (inpVec x).getD 1 false = true := by
  simp [inpVec]

private def edgeWire {V : Type} [Fintype V] (v : V) : ℕ :=
  2 + (Fintype.equivFin V v).val

private lemma edgeWire_lt {V : Type} [Fintype V] (v : V) :
    edgeWire v < 2 + Fintype.card V := by
  unfold edgeWire
  have := (Fintype.equivFin V v).isLt
  omega

private lemma inpVec_edgeWire {V : Type} [Fintype V] (x : V → Bool) (v : V) :
    (inpVec x).getD (edgeWire v) false = x v := by
  unfold inpVec edgeWire
  have hlt : (Fintype.equivFin V v).val < Fintype.card V := (Fintype.equivFin V v).isLt
  rw [Nat.add_comm 2]
  simp [List.getD_eq_getElem?_getD, hlt]

private def pigeonEdges {n : ℕ} (G : BipGraph (n + 1) n) (p : Fin (n + 1)) : List (GEdge G) :=
  (G p).attach.toList.map (fun h => ⟨(p, h.1), h.2⟩)

private lemma pigeonEdges_nodup {n : ℕ} (G : BipGraph (n + 1) n) (p : Fin (n + 1)) :
    (pigeonEdges G p).Nodup := by
  unfold pigeonEdges
  refine (Finset.nodup_toList _).map ?_
  intro a b hab
  have := congrArg (fun e : GEdge G => e.1.2) hab
  exact Subtype.ext this

private lemma pigeonEdges_length {n : ℕ} (G : BipGraph (n + 1) n) (p : Fin (n + 1)) :
    (pigeonEdges G p).length = (G p).card := by
  simp [pigeonEdges]

private lemma mem_pigeonEdges {n : ℕ} (G : BipGraph (n + 1) n) (p : Fin (n + 1)) (e : GEdge G) :
    e ∈ pigeonEdges G p ↔ e.1.1 = p := by
  unfold pigeonEdges
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨h, rfl⟩; rfl
  · intro hp
    rcases e with ⟨⟨p', q⟩, hq⟩
    dsimp only at hp
    subst hp
    exact ⟨⟨q, hq⟩, rfl⟩

private def holeEdges {n : ℕ} (G : BipGraph (n + 1) n) (h : Fin n) : List (GEdge G) :=
  (rightNbrs G h).attach.toList.map (fun p => ⟨(p.1, h), by
    have hp := p.2
    unfold rightNbrs at hp
    exact (Finset.mem_filter.mp hp).2⟩)

private lemma holeEdges_nodup {n : ℕ} (G : BipGraph (n + 1) n) (h : Fin n) :
    (holeEdges G h).Nodup := by
  unfold holeEdges
  refine (Finset.nodup_toList _).map ?_
  intro a b hab
  have := congrArg (fun e : GEdge G => e.1.1) hab
  exact Subtype.ext this

private lemma holeEdges_length {n : ℕ} (G : BipGraph (n + 1) n) (h : Fin n) :
    (holeEdges G h).length = (rightNbrs G h).card := by
  simp [holeEdges]

private lemma mem_holeEdges {n : ℕ} (G : BipGraph (n + 1) n) (h : Fin n) (e : GEdge G) :
    e ∈ holeEdges G h ↔ e.1.2 = h := by
  unfold holeEdges
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨p, rfl⟩; rfl
  · intro hh
    rcases e with ⟨⟨p, q⟩, hq⟩
    dsimp only at hh
    subst hh
    exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hq⟩⟩, rfl⟩

private lemma countP_pigeonEdges {n : ℕ} (G : BipGraph (n + 1) n) (p : Fin (n + 1))
    (x : GEdge G → Bool) :
    (pigeonEdges G p).countP (fun e => x e) =
      (Finset.univ.filter (fun e : GEdge G => e.1.1 = p ∧ x e = true)).card := by
  rw [List.countP_eq_length_filter]
  have hnd : ((pigeonEdges G p).filter (fun e => x e)).Nodup :=
    (pigeonEdges_nodup G p).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext e
  simp [mem_pigeonEdges]

private lemma countP_holeEdges {n : ℕ} (G : BipGraph (n + 1) n) (h : Fin n)
    (x : GEdge G → Bool) :
    (holeEdges G h).countP (fun e => x e) =
      (Finset.univ.filter (fun e : GEdge G => e.1.2 = h ∧ x e = true)).card := by
  rw [List.countP_eq_length_filter]
  have hnd : ((holeEdges G h).filter (fun e => x e)).Nodup :=
    (holeEdges_nodup G h).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext e
  simp [mem_holeEdges]

private lemma sum_pigeon_eq_sum_hole {n : ℕ} (G : BipGraph (n + 1) n) (x : GEdge G → Bool) :
    (∑ p : Fin (n + 1), (pigeonEdges G p).countP (fun e => x e)) =
      (∑ h : Fin n, (holeEdges G h).countP (fun e => x e)) := by
  have h1 : (∑ p : Fin (n + 1), (pigeonEdges G p).countP (fun e => x e)) =
      (Finset.univ.filter (fun e : GEdge G => x e = true)).card := by
    simp_rw [countP_pigeonEdges]
    rw [← Finset.card_biUnion]
    · congr 1; ext e; simp
    · intro p1 _ p2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he1 he2
      simp only [Finset.mem_filter] at he1 he2
      exact hne (he1.2.1.symm.trans he2.2.1)
  have h2 : (∑ h : Fin n, (holeEdges G h).countP (fun e => x e)) =
      (Finset.univ.filter (fun e : GEdge G => x e = true)).card := by
    simp_rw [countP_holeEdges]
    rw [← Finset.card_biUnion]
    · congr 1; ext e; simp
    · intro h1 _ h2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he1 he2
      simp only [Finset.mem_filter] at he1 he2
      exact hne (he1.2.1.symm.trans he2.2.1)
  exact h1.trans h2.symm

private inductive BuiltP (n : ℕ) (G : BipGraph (n + 1) n) where
  | leaf (p : Fin (n + 1)) (bits : List ℕ) (flag : ℕ)
  | node (l r : BuiltP n G) (bits : List ℕ) (flag : ℕ) (sz : ℕ)

private def BuiltP.bits {n : ℕ} {G : BipGraph (n + 1) n} : BuiltP n G → List ℕ
  | .leaf _ bs _ => bs
  | .node _ _ bs _ _ => bs

private def BuiltP.flag {n : ℕ} {G : BipGraph (n + 1) n} : BuiltP n G → ℕ
  | .leaf _ _ f => f
  | .node _ _ _ f _ => f

private def BuiltP.sz {n : ℕ} {G : BipGraph (n + 1) n} : BuiltP n G → ℕ
  | .leaf _ _ _ => 1
  | .node _ _ _ _ s => s

private def buildP {n : ℕ} (G : BipGraph (n + 1) n) (w0 : ℕ) :
    List Gate → BTree (Fin (n + 1)) → List Gate × BuiltP n G
  | gs, .leaf p =>
    let m := 2 + Fintype.card (GEdge G)
    let ws := (pigeonEdges G p).map edgeWire
    let r1 := mkSumList m w0 gs ws
    let r2 := mkLtConst m r1.1 r1.2 1
    (r2.1, .leaf p r1.2 r2.2)
  | gs, .node l r =>
    let m := 2 + Fintype.card (GEdge G)
    let rl := buildP G w0 gs l
    let rr := buildP G w0 rl.1 r
    let k := max rl.2.bits.length rr.2.bits.length
    let radd := mkAddBits m rr.1 k rl.2.bits rr.2.bits
    let sz := rl.2.sz + rr.2.sz
    let rfl := mkLtConst m radd.1 radd.2 sz
    (rfl.1, .node rl.2 rr.2 radd.2 rfl.2 sz)

private def BuiltP.Wf {n : ℕ} {G : BipGraph (n + 1) n} (m : ℕ) (gs : List Gate) :
    BuiltP n G → Prop
  | .leaf _ bs f =>
    (∀ w ∈ bs, w < m + gs.length) ∧ m ≤ f ∧ f < m + gs.length
  | .node l r bs f _ =>
    l.Wf m gs ∧ r.Wf m gs ∧
    (∀ w ∈ bs, w < m + gs.length) ∧ m ≤ f ∧ f < m + gs.length ∧
    l.flag < r.flag ∧ r.flag < f

private lemma BuiltP.wf_mono {n : ℕ} {G : BipGraph (n + 1) n} {m : ℕ} {gs1 gs2 : List Gate}
    (hle : gs1.length ≤ gs2.length) {t : BuiltP n G} (hw : t.Wf m gs1) : t.Wf m gs2 := by
  induction t with
  | leaf p bs f =>
    exact ⟨fun w h => by have := hw.1 w h; omega, hw.2.1, by have := hw.2.2; omega⟩
  | node l r bs f sz ihl ihr =>
    exact ⟨ihl hw.1, ihr hw.2.1, fun w h => by have := hw.2.2.1 w h; omega,
      hw.2.2.2.1, by have := hw.2.2.2.2.1; omega, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩

private lemma mkLtConst_flag_ge (m : ℕ) (gs : List Gate) (ws : List ℕ) (K : ℕ) :
    m + gs.length ≤ (mkLtConst m gs ws K).2 := by
  have hstep : ∀ (ls : List ℕ) (g0 : List Gate) (k acc : ℕ),
      acc ≤ (mkLtList m g0 ls k acc).2 ∨ m + g0.length ≤ (mkLtList m g0 ls k acc).2 := by
    intro ls
    induction ls with
    | nil => intro g0 k acc; exact Or.inl le_rfl
    | cons w ws' ih' =>
      intro g0 k acc
      unfold mkLtList; dsimp only
      split_ifs
      · rcases ih' (mkOr m (mkNot m g0 w).1 (mkNot m g0 w).2 acc).1 (k / 2)
          (mkOr m (mkNot m g0 w).1 (mkNot m g0 w).2 acc).2 with h | h
        · right; simp only [mkOr, mkNot, List.length_append, List.length_singleton] at h ⊢; omega
        · right; simp only [mkOr, mkNot, List.length_append, List.length_singleton] at h ⊢; omega
      · rcases ih' (mkAnd m (mkNot m g0 w).1 (mkNot m g0 w).2 acc).1 (k / 2)
          (mkAnd m (mkNot m g0 w).1 (mkNot m g0 w).2 acc).2 with h | h
        · right; simp only [mkAnd, mkNot, List.length_append, List.length_singleton] at h ⊢; omega
        · right; simp only [mkAnd, mkNot, List.length_append, List.length_singleton] at h ⊢; omega
  unfold mkLtConst; dsimp only
  rcases hstep ws (mkFalse m gs).1 K (mkFalse m gs).2 with h | h
  · simp only [mkFalse, mkAnd, List.length_append, List.length_singleton] at h ⊢; omega
  · simp only [mkFalse, mkAnd, List.length_append, List.length_singleton] at h ⊢; omega

private lemma mkGtConst_flag_ge (m : ℕ) (gs : List Gate) (ws : List ℕ) (K : ℕ) :
    m + gs.length ≤ (mkGtConst m gs ws K).2 := by
  have hstep : ∀ (ls : List ℕ) (g0 : List Gate) (k acc : ℕ),
      acc ≤ (mkGtList m g0 ls k acc).2 ∨ m + g0.length ≤ (mkGtList m g0 ls k acc).2 := by
    intro ls
    induction ls with
    | nil => intro g0 k acc; exact Or.inl le_rfl
    | cons w ws' ih' =>
      intro g0 k acc
      unfold mkGtList; dsimp only
      split_ifs
      · rcases ih' (mkAnd m g0 w acc).1 (k / 2) (mkAnd m g0 w acc).2 with h | h
        · right; simp only [mkAnd, List.length_append, List.length_singleton] at h ⊢; omega
        · right; simp only [mkAnd, List.length_append, List.length_singleton] at h ⊢; omega
      · rcases ih' (mkOr m g0 w acc).1 (k / 2) (mkOr m g0 w acc).2 with h | h
        · right; simp only [mkOr, List.length_append, List.length_singleton] at h ⊢; omega
        · right; simp only [mkOr, List.length_append, List.length_singleton] at h ⊢; omega
  unfold mkGtConst; dsimp only
  rcases hstep ws (mkFalse m gs).1 K (mkFalse m gs).2 with h | h
  · simp only [mkFalse, mkAnd, List.length_append, List.length_singleton] at h ⊢; omega
  · simp only [mkFalse, mkAnd, List.length_append, List.length_singleton] at h ⊢; omega

private lemma buildP_spec {n b w0 : ℕ} (G : BipGraph (n + 1) n)
    (hLd : LeftDegLe G b) (hw0 : b < 2 ^ w0) (hw0_pos : 1 ≤ w0)
    (t : BTree (Fin (n + 1))) (gs : List Gate)
    (hv : CValid (2 + Fintype.card (GEdge G)) gs) :
    let m := 2 + Fintype.card (GEdge G)
    let res := buildP G w0 gs t
    CValid m res.1 ∧ gs <+: res.1 ∧
    res.1.length + (13 * w0 + 15) ≤ gs.length + (5 * w0 * b + 15 * w0 + 16) * t.size + 13 * t.sumHeight ∧
    res.2.bits.length = w0 + t.height ∧
    res.2.sz = t.size ∧
    res.2.Wf m res.1 ∧
    m + gs.length ≤ res.2.flag ∧
    ∀ x : GEdge G → Bool,
      bitsVal res.1 (inpVec x) res.2.bits =
        (t.leaves.map (fun p => (pigeonEdges G p).countP (fun e => x e))).sum ∧
      wVal res.1 (inpVec x) res.2.flag =
        decide (bitsVal res.1 (inpVec x) res.2.bits < t.size) := by
  induction t generalizing gs with
  | leaf p =>
    unfold buildP; dsimp only
    set m := 2 + Fintype.card (GEdge G)
    have hm : 2 ≤ m := by omega
    set ws := (pigeonEdges G p).map edgeWire
    have hws_lt : ∀ w ∈ ws, w < m + gs.length := by
      intro w hw
      simp only [ws, List.mem_map] at hw
      rcases hw with ⟨e, _, rfl⟩
      have := edgeWire_lt e; omega
    have hws_len : ws.length ≤ b := by
      simp only [ws, List.length_map, pigeonEdges_length]
      exact hLd p
    have hws_pow : ws.length < 2 ^ w0 := lt_of_le_of_lt hws_len hw0
    set r1 := mkSumList m w0 gs ws with hr1
    have h1 := mkSumList_spec hm hv hws_lt hws_pow; dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨h1v, h1p, h1l, h1bl, h1bw, h1val⟩
    have h1K : 1 < 2 ^ r1.2.length := by
      rw [h1bl]
      have : 2 ^ 1 ≤ 2 ^ w0 := Nat.pow_le_pow_right (by omega) hw0_pos
      omega
    set r2 := mkLtConst m r1.1 r1.2 1 with hr2
    have h2 := mkLtConst_spec hm h1v h1bw h1K; dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
    have hflag_ge : m + gs.length ≤ r2.2 := by
      have := mkLtConst_flag_ge m r1.1 r1.2 1; rw [← hr2] at this; omega
    refine ⟨h2v, h1p.trans h2p, ?_, by simp [BuiltP.bits, BTree.height, h1bl],
      rfl, ⟨fun w hw => by have := h1bw w hw; omega, h2ge, h2lt⟩,
      hflag_ge, fun x => ?_⟩
    · simp only [BTree.size, BTree.sumHeight, mul_one, mul_zero, add_zero]
      have hmul : 5 * w0 * ws.length ≤ 5 * w0 * b := Nat.mul_le_mul_left _ hws_len
      rw [h2l, h1l, h1bl]
      omega
    · have hbv : bitsVal r2.1 (inpVec x) r1.2 = (pigeonEdges G p).countP (fun e => x e) := by
        rw [bitsVal_prefix h2p (inpVec_length x) h1bw,
            h1val (inpVec x) (inpVec_length x) (inpVec_zero x)]
        simp only [ws, List.countP_map]
        congr 1
        funext e
        simp only [Function.comp_apply]
        rw [wVal_input gs (inpVec x) (by rw [inpVec_length]; exact edgeWire_lt e), inpVec_edgeWire]
      refine ⟨by simpa [BuiltP.bits, BTree.leaves] using hbv, ?_⟩
      dsimp only [BuiltP.flag, BuiltP.bits, BTree.size]
      rw [h2val (inpVec x) (inpVec_length x) (inpVec_zero x)]
      by_cases hlt : bitsVal r1.1 (inpVec x) r1.2 < 1
      · rw [decide_eq_true hlt]; symm; exact decide_eq_true (by rwa [bitsVal_prefix h2p (inpVec_length x) h1bw])
      · rw [decide_eq_false hlt]; symm; exact decide_eq_false (by rwa [bitsVal_prefix h2p (inpVec_length x) h1bw])
  | node l r ihl ihr =>
    unfold buildP; dsimp only
    set m := 2 + Fintype.card (GEdge G)
    have hm : 2 ≤ m := by omega
    set rl := buildP G w0 gs l with hrl
    have hl := ihl gs hv; dsimp only at hl; rw [← hrl] at hl
    rcases hl with ⟨hlv, hlp, hllen, hlbl, hlsz, hlwf, hlfg, hlval⟩
    set rr := buildP G w0 rl.1 r with hrr
    have hr := ihr rl.1 hlv; dsimp only at hr; rw [← hrr] at hr
    rcases hr with ⟨hrv, hrp, hrlen, hrbl, hrsz, hrwf, hrfg, hrval⟩
    set k := max rl.2.bits.length rr.2.bits.length
    have hk_eq : max rl.2.bits.length rr.2.bits.length = w0 + max l.height r.height := by
      rw [hlbl, hrbl]; omega
    have hlb_lt0 : ∀ w ∈ rl.2.bits, w < m + rl.1.length := fun w hw => by
      cases hlt : rl.2 with
      | leaf _ bs f => rw [hlt] at hlwf; exact hlwf.1 w (by simpa [hlt, BuiltP.bits] using hw)
      | node _ _ bs f _ => rw [hlt] at hlwf; exact hlwf.2.2.1 w (by simpa [hlt, BuiltP.bits] using hw)
    have hr_len_le : rl.1.length ≤ rr.1.length := List.IsPrefix.length_le hrp
    have hlb_lt : ∀ w ∈ rl.2.bits, w < m + rr.1.length := fun w hw => by
      have := hlb_lt0 w hw; omega
    have hrb_lt : ∀ w ∈ rr.2.bits, w < m + rr.1.length := fun w hw => by
      cases hrt : rr.2 with
      | leaf _ bs f => rw [hrt] at hrwf; exact hrwf.1 w (by simpa [hrt, BuiltP.bits] using hw)
      | node _ _ bs f _ => rw [hrt] at hrwf; exact hrwf.2.2.1 w (by simpa [hrt, BuiltP.bits] using hw)
    set radd := mkAddBits m rr.1 k rl.2.bits rr.2.bits with hradd
    have hadd := mkAddBits_spec hm hrv (le_max_left _ _) (le_max_right _ _) hlb_lt hrb_lt
    dsimp only at hadd; rw [← hradd] at hadd
    rcases hadd with ⟨haddv, haddp, haddl, haddbl, haddbw, haddval⟩
    set sz := rl.2.sz + rr.2.sz
    have hsz_eq : sz = l.size + r.size := by simp [sz, hlsz, hrsz]
    have hsz_lt : sz < 2 ^ radd.2.length := by
      rw [haddbl, hk_eq, hsz_eq]
      have h1 := l.size_le_pow_height
      have h2 := r.size_le_pow_height
      have hm1 : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
        Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have hm2 : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
        Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have hw2 : 2 ≤ 2 ^ w0 := by
        have := Nat.pow_le_pow_right (by omega : 0 < 2) hw0_pos
        simpa using this
      have hpow : 2 ^ (w0 + max l.height r.height + 1) = 2 ^ w0 * (2 * 2 ^ max l.height r.height) := by
        rw [pow_succ', pow_add]; ring
      rw [hpow]
      have hsum : l.size + r.size ≤ 2 * 2 ^ max l.height r.height := by omega
      have hpos : 0 < 2 * 2 ^ max l.height r.height := by positivity
      exact lt_of_le_of_lt hsum (lt_mul_of_one_lt_left hpos (by omega))
    set rf := mkLtConst m radd.1 radd.2 sz with hrf
    have hf := mkLtConst_spec hm haddv haddbw hsz_lt; dsimp only at hf; rw [← hrf] at hf
    rcases hf with ⟨hfv, hfp, hfl, hfge, hflt, hfval⟩
    have hfl_ge_add : m + radd.1.length ≤ rf.2 := by
      have := mkLtConst_flag_ge m radd.1 radd.2 sz; rw [← hrf] at this; exact this
    have hl_fl_lt : rl.2.flag < m + rl.1.length := by
      cases hlt : rl.2 with
      | leaf _ _ _ => rw [hlt] at hlwf; exact hlwf.2.2
      | node _ _ _ _ _ => rw [hlt] at hlwf; exact hlwf.2.2.2.2.1
    have hr_fl_lt : rr.2.flag < m + rr.1.length := by
      cases hrt : rr.2 with
      | leaf _ _ _ => rw [hrt] at hrwf; exact hrwf.2.2
      | node _ _ _ _ _ => rw [hrt] at hrwf; exact hrwf.2.2.2.2.1
    have hl_len_le : gs.length ≤ rl.1.length := List.IsPrefix.length_le hlp
    have hadd_len_le : rr.1.length ≤ radd.1.length := List.IsPrefix.length_le haddp
    have hfl_len_le : radd.1.length ≤ rf.1.length := List.IsPrefix.length_le hfp
    refine ⟨hfv, hlp.trans (hrp.trans (haddp.trans hfp)), ?_,
      by dsimp only [BuiltP.bits, BTree.height]; rw [haddbl, hk_eq]; omega,
      by simp [BuiltP.sz, BTree.size, hsz_eq],
      ⟨BuiltP.wf_mono (by omega) hlwf, BuiltP.wf_mono (by omega) hrwf,
       fun w hw => by have := haddbw w hw; omega,
       hfge, hflt, by omega, by omega⟩,
      by dsimp only [BuiltP.flag]; omega, fun x => ?_⟩
    · simp only [BTree.size, BTree.sumHeight]
      change rf.1.length + (13 * w0 + 15) ≤ _
      rw [hfl, haddl, haddbl, hk_eq, mul_add (5 * w0 * b + 15 * w0 + 16)]
      omega
    · have hbv : bitsVal rf.1 (inpVec x) radd.2 =
          (l.leaves.map (fun p => (pigeonEdges G p).countP (fun e => x e))).sum +
          (r.leaves.map (fun p => (pigeonEdges G p).countP (fun e => x e))).sum := by
        rw [bitsVal_prefix hfp (inpVec_length x) haddbw,
            haddval (inpVec x) (inpVec_length x) (inpVec_zero x),
            bitsVal_prefix hrp (inpVec_length x) hlb_lt0,
            (hlval x).1, (hrval x).1]
      refine ⟨by simpa only [BuiltP.bits, BTree.leaves, List.map_append, List.sum_append] using hbv, ?_⟩
      dsimp only [BuiltP.flag, BuiltP.bits, BTree.size]
      rw [hfval (inpVec x) (inpVec_length x) (inpVec_zero x)]
      by_cases hlt : bitsVal radd.1 (inpVec x) radd.2 < sz
      · rw [decide_eq_true hlt]; symm; exact decide_eq_true (by rw [bitsVal_prefix hfp (inpVec_length x) haddbw, ← hsz_eq]; exact hlt)
      · rw [decide_eq_false hlt]; symm; exact decide_eq_false (by rw [bitsVal_prefix hfp (inpVec_length x) haddbw, ← hsz_eq]; exact hlt)

private inductive BuiltH (n : ℕ) (G : BipGraph (n + 1) n) where
  | leaf (h : Fin n) (bits : List ℕ) (sFlags tFlags : List ℕ)
  | node (l r : BuiltH n G) (bits : List ℕ) (flag : ℕ) (sz : ℕ)

private def BuiltH.bits {n : ℕ} {G : BipGraph (n + 1) n} : BuiltH n G → List ℕ
  | .leaf _ bs _ _ => bs
  | .node _ _ bs _ _ => bs

private def BuiltH.flag {n : ℕ} {G : BipGraph (n + 1) n} : BuiltH n G → ℕ
  | .leaf _ _ _ tf => tf.headD 0
  | .node _ _ _ f _ => f

private def BuiltH.sz {n : ℕ} {G : BipGraph (n + 1) n} : BuiltH n G → ℕ
  | .leaf _ _ _ _ => 1
  | .node _ _ _ _ s => s

private def buildH {n : ℕ} (G : BipGraph (n + 1) n) (w0 : ℕ) :
    List Gate → BTree (Fin n) → List Gate × BuiltH n G
  | gs, .leaf h =>
    let m := 2 + Fintype.card (GEdge G)
    let ws := (holeEdges G h).map edgeWire
    let r1 := mkSumList m w0 gs ws
    let r2 := mkHoleFlags m r1.1 ws
    (r2.1, .leaf h r1.2 r2.2.1 r2.2.2)
  | gs, .node l r =>
    let m := 2 + Fintype.card (GEdge G)
    let rl := buildH G w0 gs l
    let rr := buildH G w0 rl.1 r
    let k := max rl.2.bits.length rr.2.bits.length
    let radd := mkAddBits m rr.1 k rl.2.bits rr.2.bits
    let sz := rl.2.sz + rr.2.sz
    let rfl := mkGtConst m radd.1 radd.2 sz
    (rfl.1, .node rl.2 rr.2 radd.2 rfl.2 sz)

private def BuiltH.Wf {n : ℕ} {G : BipGraph (n + 1) n} (m : ℕ) (gs : List Gate) :
    BuiltH n G → Prop
  | .leaf h bs sf tf =>
    (∀ w ∈ bs, w < m + gs.length) ∧
    sf.length = (holeEdges G h).length + 1 ∧ tf.length = (holeEdges G h).length + 1 ∧
    (∀ u ∈ sf, m ≤ u ∧ u < m + gs.length) ∧ (∀ u ∈ tf, m ≤ u ∧ u < m + gs.length) ∧
    sf.Nodup ∧ tf.Nodup ∧ (∀ u ∈ sf, u ∉ tf) ∧
    ∀ x : GEdge G → Bool,
      wVal gs (inpVec x) (sf.getLastD 0) = false ∧
      wVal gs (inpVec x) (tf.getLastD 0) = false ∧
      ∀ k : ℕ, (hk : k < (holeEdges G h).length) →
        wVal gs (inpVec x) (sf.getD k 0) =
          (wVal gs (inpVec x) (sf.getD (k + 1) 0) || x ((holeEdges G h)[k])) ∧
        wVal gs (inpVec x) (tf.getD k 0) =
          (wVal gs (inpVec x) (tf.getD (k + 1) 0) ||
            (wVal gs (inpVec x) (sf.getD (k + 1) 0) && x ((holeEdges G h)[k])))
  | .node l r bs f _ =>
    l.Wf m gs ∧ r.Wf m gs ∧
    (∀ w ∈ bs, w < m + gs.length) ∧ m ≤ f ∧ f < m + gs.length ∧
    l.flag < r.flag ∧ r.flag < f

private lemma BuiltH.flag_lt {n : ℕ} {G : BipGraph (n + 1) n} {m : ℕ} {gs : List Gate}
    {t : BuiltH n G} (hw : t.Wf m gs) : m ≤ t.flag ∧ t.flag < m + gs.length := by
  cases t with
  | leaf h bs sf tf =>
    simp only [BuiltH.flag]
    have hmem : tf.headD 0 ∈ tf := by
      cases htf : tf with
      | nil => have := hw.2.2.1; rw [htf] at this; simp at this
      | cons _ _ => simp
    exact hw.2.2.2.2.1 _ hmem
  | node _ _ _ _ _ => exact ⟨hw.2.2.2.1, hw.2.2.2.2.1⟩

private lemma getLastD_mem_of_ne_nil {α : Type} {l : List α} (hne : l ≠ []) (d : α) :
    l.getLastD d ∈ l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a as ih =>
    cases as with
    | nil => simp [List.getLastD]
    | cons b bs =>
      have : (a :: b :: bs).getLastD d = (b :: bs).getLastD d := rfl
      rw [this]
      exact List.mem_cons_of_mem a (ih (by simp))

private lemma BuiltH.wf_prefix {n : ℕ} {G : BipGraph (n + 1) n} {m : ℕ} {gs1 gs2 : List Gate}
    (hm : m = 2 + Fintype.card (GEdge G)) (hp : gs1 <+: gs2)
    {t : BuiltH n G} (hw : t.Wf m gs1) : t.Wf m gs2 := by
  have hle := List.IsPrefix.length_le hp
  induction t with
  | leaf h bs sf tf =>
    refine ⟨fun w h' => by have := hw.1 w h'; omega, hw.2.1, hw.2.2.1,
      fun u hu => ⟨(hw.2.2.2.1 u hu).1, by have := (hw.2.2.2.1 u hu).2; omega⟩,
      fun u hu => ⟨(hw.2.2.2.2.1 u hu).1, by have := (hw.2.2.2.2.1 u hu).2; omega⟩,
      hw.2.2.2.2.2.1, hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, fun x => ?_⟩
    have hx := hw.2.2.2.2.2.2.2.2 x
    have hsf_len := hw.2.1
    have htf_len := hw.2.2.1
    have hsf_last : sf.getLastD 0 ∈ sf :=
      getLastD_mem_of_ne_nil (fun h => by rw [h] at hsf_len; simp at hsf_len) 0
    have htf_last : tf.getLastD 0 ∈ tf :=
      getLastD_mem_of_ne_nil (fun h => by rw [h] at htf_len; simp at htf_len) 0
    refine ⟨by rw [wVal_prefix hp (by rw [inpVec_length, ← hm]) (hw.2.2.2.1 _ hsf_last).2]; exact hx.1,
      by rw [wVal_prefix hp (by rw [inpVec_length, ← hm]) (hw.2.2.2.2.1 _ htf_last).2]; exact hx.2.1,
      fun k hk => ?_⟩
    have hk1 : k < sf.length := by omega
    have hk2 : k + 1 < sf.length := by omega
    have hkt1 : k < tf.length := by omega
    have hkt2 : k + 1 < tf.length := by omega
    have hmem_s1 : sf.getD k 0 ∈ sf := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]; exact List.getElem_mem hk1
    have hmem_s2 : sf.getD (k + 1) 0 ∈ sf := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2]; exact List.getElem_mem hk2
    have hmem_t1 : tf.getD k 0 ∈ tf := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkt1]; exact List.getElem_mem hkt1
    have hmem_t2 : tf.getD (k + 1) 0 ∈ tf := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkt2]; exact List.getElem_mem hkt2
    rw [wVal_prefix hp (by rw [inpVec_length, ← hm]) (hw.2.2.2.1 _ hmem_s1).2,
        wVal_prefix hp (by rw [inpVec_length, ← hm]) (hw.2.2.2.1 _ hmem_s2).2,
        wVal_prefix hp (by rw [inpVec_length, ← hm]) (hw.2.2.2.2.1 _ hmem_t1).2,
        wVal_prefix hp (by rw [inpVec_length, ← hm]) (hw.2.2.2.2.1 _ hmem_t2).2]
    exact hx.2.2 k hk
  | node l r bs f sz ihl ihr =>
    exact ⟨ihl hw.1, ihr hw.2.1, fun w h' => by have := hw.2.2.1 w h'; omega,
      hw.2.2.2.1, by have := hw.2.2.2.2.1; omega, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩

private lemma mkHoleFlags_recurrence {m : ℕ} (hm : 2 ≤ m) {gs : List Gate} (hv : CValid m gs)
    {ws : List ℕ} (hws : ∀ w ∈ ws, w < m + gs.length)
    (inp : List Bool) (hinp : inp.length = m) (h0i : inp.getD 0 false = false) :
    let r := mkHoleFlags m gs ws
    wVal r.1 inp (r.2.1.getLastD 0) = false ∧
    wVal r.1 inp (r.2.2.getLastD 0) = false ∧
    ∀ k : ℕ, (hk : k < ws.length) →
      wVal r.1 inp (r.2.1.getD k 0) =
        (wVal r.1 inp (r.2.1.getD (k + 1) 0) || wVal gs inp (ws[k])) ∧
      wVal r.1 inp (r.2.2.getD k 0) =
        (wVal r.1 inp (r.2.2.getD (k + 1) 0) ||
          (wVal r.1 inp (r.2.1.getD (k + 1) 0) && wVal gs inp (ws[k]))) := by
  induction ws generalizing gs with
  | nil =>
    unfold mkHoleFlags; dsimp only
    set r1 := mkFalse m gs with hr1
    have h1 := mkFalse_spec hm hv; dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨h1v, h1p, h1l, h1ge, h1lt, h1val⟩
    set r2 := mkFalse m r1.1 with hr2
    have h2 := mkFalse_spec hm h1v; dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨h2v, h2p, h2l, h2ge, h2lt, h2val⟩
    refine ⟨?_, ?_, fun k hk => by simp at hk⟩
    · simp only [List.getLastD, List.getLast_singleton]
      rw [wVal_prefix h2p hinp h1lt, h1val inp hinp h0i]
    · simp only [List.getLastD, List.getLast_singleton]
      exact h2val inp hinp h0i
  | cons w ws ih =>
    unfold mkHoleFlags; dsimp only
    set r0 := mkHoleFlags m gs ws with hr0
    have h0 := mkHoleFlags_spec hm hv (ws := ws) (fun u hu => hws u (by simp [hu])); dsimp only at h0; rw [← hr0] at h0
    rcases h0 with ⟨h0v, h0p, h0l, h0sl, h0tl, h0sb, h0tb, h0snd, h0tnd, h0disj, h0sge, h0tge, h0val⟩
    have hih := ih hv (fun u hu => hws u (by simp [hu])); dsimp only at hih; rw [← hr0] at hih
    have hs_mem : r0.2.1.headD 0 ∈ r0.2.1 := by
      cases h : r0.2.1 with
      | nil => rw [h] at h0sl; simp at h0sl
      | cons _ _ => simp
    have ht_mem : r0.2.2.headD 0 ∈ r0.2.2 := by
      cases h : r0.2.2 with
      | nil => rw [h] at h0tl; simp at h0tl
      | cons _ _ => simp
    have hs_lt := (h0sb _ hs_mem).2
    have ht_lt := (h0tb _ ht_mem).2
    have hw_lt : w < m + r0.1.length := by have := hws w (by simp); omega
    set rs := mkOr m r0.1 (r0.2.1.headD 0) w with hrs
    have hrs_h := mkOr_spec h0v hs_lt hw_lt; dsimp only at hrs_h; rw [← hrs] at hrs_h
    rcases hrs_h with ⟨hrsv, hrsp, hrsl, hrsge, hrslt, hrsval⟩
    set rp := mkAnd m rs.1 (r0.2.1.headD 0) w with hrp
    have hrp_h := mkAnd_spec hrsv (u := r0.2.1.headD 0) (v := w) (by omega) (by omega); dsimp only at hrp_h; rw [← hrp] at hrp_h
    rcases hrp_h with ⟨hrpv, hrpp, hrpl, hrpge, hrplt, hrpval⟩
    set rt := mkOr m rp.1 (r0.2.2.headD 0) rp.2 with hrt
    have hrt_h := mkOr_spec hrpv (u := r0.2.2.headD 0) (v := rp.2) (by omega) hrplt; dsimp only at hrt_h; rw [← hrt] at hrt_h
    rcases hrt_h with ⟨hrtv, hrtp, hrtl, hrtge, hrtlt, hrtval⟩
    have hpref : r0.1 <+: rt.1 := hrsp.trans (hrpp.trans hrtp)
    have hne_s : r0.2.1 ≠ [] := by
      intro h; rw [h] at h0sl; simp at h0sl
    have hne_t : r0.2.2 ≠ [] := by
      intro h; rw [h] at h0tl; simp at h0tl
    have hlast_s : (rs.2 :: r0.2.1).getLastD 0 = r0.2.1.getLastD 0 := by
      cases h : r0.2.1 with
      | nil => exact absurd h hne_s
      | cons a as => rfl
    have hlast_t : (rt.2 :: r0.2.2).getLastD 0 = r0.2.2.getLastD 0 := by
      cases h : r0.2.2 with
      | nil => exact absurd h hne_t
      | cons a as => rfl
    have hls_mem : r0.2.1.getLastD 0 ∈ r0.2.1 := getLastD_mem_of_ne_nil hne_s 0
    have hlt_mem : r0.2.2.getLastD 0 ∈ r0.2.2 := getLastD_mem_of_ne_nil hne_t 0
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · rw [hlast_s, wVal_prefix hpref hinp (h0sb _ hls_mem).2]; exact hih.1
    · rw [hlast_t, wVal_prefix hpref hinp (h0tb _ hlt_mem).2]; exact hih.2.1
    · cases k with
      | zero =>
        simp only [List.getD_cons_zero, List.getD_cons_succ, List.getElem_cons_zero]
        have hhd_s : r0.2.1.getD 0 0 = r0.2.1.headD 0 := by cases r0.2.1 <;> rfl
        have hhd_t : r0.2.2.getD 0 0 = r0.2.2.headD 0 := by cases r0.2.2 <;> rfl
        rw [hhd_s, hhd_t]
        rw [wVal_prefix (hrpp.trans hrtp) hinp hrslt,
            hrsval inp hinp,
            wVal_prefix hpref hinp hs_lt, wVal_prefix hpref hinp ht_lt,
            wVal_prefix h0p hinp (hws w (by simp)),
            hrtval inp hinp,
            wVal_prefix (hrsp.trans hrpp) hinp ht_lt,
            hrpval inp hinp,
            wVal_prefix hrsp hinp hs_lt, wVal_prefix hrsp hinp hw_lt,
            wVal_prefix h0p hinp (hws w (by simp))]
        exact ⟨rfl, rfl⟩
      | succ k' =>
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        have hk' : k' < ws.length := by simp at hk; omega
        have hms1 : r0.2.1.getD k' 0 ∈ r0.2.1 := by
          have : k' < r0.2.1.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; exact List.getElem_mem this
        have hms2 : r0.2.1.getD (k' + 1) 0 ∈ r0.2.1 := by
          have : k' + 1 < r0.2.1.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; exact List.getElem_mem this
        have hmt1 : r0.2.2.getD k' 0 ∈ r0.2.2 := by
          have : k' < r0.2.2.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; exact List.getElem_mem this
        have hmt2 : r0.2.2.getD (k' + 1) 0 ∈ r0.2.2 := by
          have : k' + 1 < r0.2.2.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; exact List.getElem_mem this
        rw [wVal_prefix hpref hinp (h0sb _ hms1).2,
            wVal_prefix hpref hinp (h0sb _ hms2).2,
            wVal_prefix hpref hinp (h0tb _ hmt1).2,
            wVal_prefix hpref hinp (h0tb _ hmt2).2]
        exact hih.2.2 k' hk'

private lemma buildH_spec {n b w0 : ℕ} (G : BipGraph (n + 1) n)
    (hRd : RightDegLe G b) (hw0 : b < 2 ^ w0) (hw0_pos : 1 ≤ w0)
    (t : BTree (Fin n)) (gs : List Gate)
    (hv : CValid (2 + Fintype.card (GEdge G)) gs) :
    let m := 2 + Fintype.card (GEdge G)
    let res := buildH G w0 gs t
    CValid m res.1 ∧ gs <+: res.1 ∧
    res.1.length + (13 * w0 + 14) ≤ gs.length + (5 * w0 * b + 3 * b + 15 * w0 + 16) * t.size + 13 * t.sumHeight ∧
    res.2.bits.length = w0 + t.height ∧
    res.2.sz = t.size ∧
    res.2.Wf m res.1 ∧
    m + gs.length ≤ res.2.flag ∧
    ∀ x : GEdge G → Bool,
      bitsVal res.1 (inpVec x) res.2.bits =
        (t.leaves.map (fun h => (holeEdges G h).countP (fun e => x e))).sum ∧
      wVal res.1 (inpVec x) res.2.flag =
        decide (t.size < bitsVal res.1 (inpVec x) res.2.bits) := by
  induction t generalizing gs with
  | leaf h =>
    unfold buildH; dsimp only
    set m := 2 + Fintype.card (GEdge G)
    have hm : 2 ≤ m := by omega
    set ws := (holeEdges G h).map edgeWire
    have hws_lt : ∀ w ∈ ws, w < m + gs.length := by
      intro w hw
      simp only [ws, List.mem_map] at hw
      rcases hw with ⟨e, _, rfl⟩
      have := edgeWire_lt e; omega
    have hws_len : ws.length ≤ b := by
      simp only [ws, List.length_map, holeEdges_length]
      exact hRd h
    have hws_pow : ws.length < 2 ^ w0 := lt_of_le_of_lt hws_len hw0
    set r1 := mkSumList m w0 gs ws with hr1
    have h1 := mkSumList_spec hm hv hws_lt hws_pow; dsimp only at h1; rw [← hr1] at h1
    rcases h1 with ⟨h1v, h1p, h1l, h1bl, h1bw, h1val⟩
    have hws_lt1 : ∀ w ∈ ws, w < m + r1.1.length := fun w hw => by have := hws_lt w hw; omega
    set r2 := mkHoleFlags m r1.1 ws with hr2
    have h2 := mkHoleFlags_spec hm h1v hws_lt1; dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨h2v, h2p, h2l, h2sl, h2tl, h2sb, h2tb, h2snd, h2tnd, h2disj, h2sge, h2tge, h2val⟩
    have htf_hd : r2.2.2.headD 0 ∈ r2.2.2 := by
      cases htf : r2.2.2 with
      | nil => rw [htf] at h2tl; simp at h2tl
      | cons _ _ => simp
    have hflag_ge : m + gs.length ≤ r2.2.2.headD 0 := by
      have := h2tge _ htf_hd; omega
    refine ⟨h2v, h1p.trans h2p, ?_, by simp [BuiltH.bits, BTree.height, h1bl],
      rfl, ?_, hflag_ge, fun x => ?_⟩
    · simp only [BTree.size, BTree.sumHeight, mul_one, mul_zero, add_zero]
      have hmul1 : 5 * w0 * ws.length ≤ 5 * w0 * b := Nat.mul_le_mul_left _ hws_len
      rw [h2l, h1l]
      omega
    · refine ⟨fun w hw => by have := h1bw w hw; omega,
        by simpa [ws] using h2sl, by simpa [ws] using h2tl,
        h2sb, h2tb, h2snd, h2tnd, h2disj, fun x => ?_⟩
      have hrec := mkHoleFlags_recurrence hm h1v hws_lt1 (inpVec x) (inpVec_length x) (inpVec_zero x)
      dsimp only at hrec; rw [← hr2] at hrec
      refine ⟨hrec.1, hrec.2.1, fun k hk => ?_⟩
      have hk' : k < ws.length := by simpa [ws] using hk
      have hrk := hrec.2.2 k hk'
      have hval_e : wVal r1.1 (inpVec x) (ws[k]'hk') = x ((holeEdges G h)[k]'hk) := by
        simp only [ws, List.getElem_map]
        rw [wVal_input r1.1 (inpVec x) (by rw [inpVec_length]; exact edgeWire_lt _), inpVec_edgeWire]
      rw [hval_e] at hrk
      exact hrk
    · have hcnt : ws.countP (fun w => wVal gs (inpVec x) w) = (holeEdges G h).countP (fun e => x e) := by
        simp only [ws, List.countP_map]
        congr 1; funext e; simp only [Function.comp_apply]
        rw [wVal_input gs (inpVec x) (by rw [inpVec_length]; exact edgeWire_lt e), inpVec_edgeWire]
      have hbv : bitsVal r2.1 (inpVec x) r1.2 = (holeEdges G h).countP (fun e => x e) := by
        rw [bitsVal_prefix h2p (inpVec_length x) h1bw,
            h1val (inpVec x) (inpVec_length x) (inpVec_zero x), hcnt]
      refine ⟨by simpa only [BuiltH.bits, BTree.leaves, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using hbv, ?_⟩
      dsimp only [BuiltH.flag, BuiltH.bits, BTree.size]
      rw [(h2val (inpVec x) (inpVec_length x) (inpVec_zero x)).2]
      have hcnt1 : ws.countP (fun w => wVal r1.1 (inpVec x) w) = (holeEdges G h).countP (fun e => x e) := by
        simp only [ws, List.countP_map]
        congr 1; funext e; simp only [Function.comp_apply]
        rw [wVal_input r1.1 (inpVec x) (by rw [inpVec_length]; exact edgeWire_lt e), inpVec_edgeWire]
      by_cases hge2 : 2 ≤ ws.countP (fun w => wVal r1.1 (inpVec x) w)
      · rw [decide_eq_true hge2]; symm; exact decide_eq_true (by rw [hcnt1] at hge2; rw [hbv]; omega)
      · rw [decide_eq_false hge2]; symm; exact decide_eq_false (by rw [hcnt1] at hge2; rw [hbv]; omega)
  | node l r ihl ihr =>
    unfold buildH; dsimp only
    set m := 2 + Fintype.card (GEdge G)
    have hm : 2 ≤ m := by omega
    set rl := buildH G w0 gs l with hrl
    have hl := ihl gs hv; dsimp only at hl; rw [← hrl] at hl
    rcases hl with ⟨hlv, hlp, hllen, hlbl, hlsz, hlwf, hlfg, hlval⟩
    set rr := buildH G w0 rl.1 r with hrr
    have hr := ihr rl.1 hlv; dsimp only at hr; rw [← hrr] at hr
    rcases hr with ⟨hrv, hrp, hrlen, hrbl, hrsz, hrwf, hrfg, hrval⟩
    set k := max rl.2.bits.length rr.2.bits.length
    have hk_eq : max rl.2.bits.length rr.2.bits.length = w0 + max l.height r.height := by
      rw [hlbl, hrbl]; omega
    have hlb_lt0 : ∀ w ∈ rl.2.bits, w < m + rl.1.length := fun w hw => by
      cases hlt : rl.2 with
      | leaf _ bs _ _ => rw [hlt] at hlwf; exact hlwf.1 w (by simpa [hlt, BuiltH.bits] using hw)
      | node _ _ bs _ _ => rw [hlt] at hlwf; exact hlwf.2.2.1 w (by simpa [hlt, BuiltH.bits] using hw)
    have hr_len_le : rl.1.length ≤ rr.1.length := List.IsPrefix.length_le hrp
    have hlb_lt : ∀ w ∈ rl.2.bits, w < m + rr.1.length := fun w hw => by
      have := hlb_lt0 w hw; omega
    have hrb_lt : ∀ w ∈ rr.2.bits, w < m + rr.1.length := fun w hw => by
      cases hrt : rr.2 with
      | leaf _ bs _ _ => rw [hrt] at hrwf; exact hrwf.1 w (by simpa [hrt, BuiltH.bits] using hw)
      | node _ _ bs _ _ => rw [hrt] at hrwf; exact hrwf.2.2.1 w (by simpa [hrt, BuiltH.bits] using hw)
    set radd := mkAddBits m rr.1 k rl.2.bits rr.2.bits with hradd
    have hadd := mkAddBits_spec hm hrv (le_max_left _ _) (le_max_right _ _) hlb_lt hrb_lt
    dsimp only at hadd; rw [← hradd] at hadd
    rcases hadd with ⟨haddv, haddp, haddl, haddbl, haddbw, haddval⟩
    set sz := rl.2.sz + rr.2.sz
    have hsz_eq : sz = l.size + r.size := by simp [sz, hlsz, hrsz]
    have hsz_lt : sz < 2 ^ radd.2.length := by
      rw [haddbl, hk_eq, hsz_eq]
      have h1 := l.size_le_pow_height
      have h2 := r.size_le_pow_height
      have hm1 : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
        Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have hm2 : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
        Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have hw2 : 2 ≤ 2 ^ w0 := by
        have := Nat.pow_le_pow_right (by omega : 0 < 2) hw0_pos
        simpa using this
      have hpow : 2 ^ (w0 + max l.height r.height + 1) = 2 ^ w0 * (2 * 2 ^ max l.height r.height) := by
        rw [pow_succ', pow_add]; ring
      rw [hpow]
      have hsum : l.size + r.size ≤ 2 * 2 ^ max l.height r.height := by omega
      have hpos : 0 < 2 * 2 ^ max l.height r.height := by positivity
      exact lt_of_le_of_lt hsum (lt_mul_of_one_lt_left hpos (by omega))
    set rf := mkGtConst m radd.1 radd.2 sz with hrf
    have hf := mkGtConst_spec hm haddv haddbw hsz_lt; dsimp only at hf; rw [← hrf] at hf
    rcases hf with ⟨hfv, hfp, hfl, hfge, hflt, hfval⟩
    have hfl_ge_add : m + radd.1.length ≤ rf.2 := by
      have := mkGtConst_flag_ge m radd.1 radd.2 sz; rw [← hrf] at this; exact this
    have hl_fl_lt := (BuiltH.flag_lt hlwf).2
    have hr_fl_lt := (BuiltH.flag_lt hrwf).2
    have hl_len_le := List.IsPrefix.length_le hlp
    have hadd_len_le := List.IsPrefix.length_le haddp
    have hfl_len_le := List.IsPrefix.length_le hfp
    refine ⟨hfv, hlp.trans (hrp.trans (haddp.trans hfp)), ?_,
      by dsimp only [BuiltH.bits, BTree.height]; rw [haddbl, hk_eq]; omega,
      by simp [BuiltH.sz, BTree.size, hsz_eq],
      ⟨BuiltH.wf_prefix rfl (hrp.trans (haddp.trans hfp)) hlwf,
       BuiltH.wf_prefix rfl (haddp.trans hfp) hrwf,
       fun w hw => by have := haddbw w hw; omega,
       hfge, hflt, by omega, by omega⟩,
      by dsimp only [BuiltH.flag]; omega, fun x => ?_⟩
    · simp only [BTree.size, BTree.sumHeight]
      change rf.1.length + (13 * w0 + 14) ≤ _
      rw [hfl, haddl, haddbl, hk_eq, mul_add (5 * w0 * b + 3 * b + 15 * w0 + 16)]
      omega
    · have hbv : bitsVal rf.1 (inpVec x) radd.2 =
          (l.leaves.map (fun h => (holeEdges G h).countP (fun e => x e))).sum +
          (r.leaves.map (fun h => (holeEdges G h).countP (fun e => x e))).sum := by
        rw [bitsVal_prefix hfp (inpVec_length x) haddbw,
            haddval (inpVec x) (inpVec_length x) (inpVec_zero x),
            bitsVal_prefix hrp (inpVec_length x) hlb_lt0,
            (hlval x).1, (hrval x).1]
      refine ⟨by simpa only [BuiltH.bits, BTree.leaves, List.map_append, List.sum_append] using hbv, ?_⟩
      dsimp only [BuiltH.flag, BuiltH.bits, BTree.size]
      rw [hfval (inpVec x) (inpVec_length x) (inpVec_zero x)]
      by_cases hgt : sz < bitsVal radd.1 (inpVec x) radd.2
      · rw [decide_eq_true hgt]; symm; exact decide_eq_true (by rw [bitsVal_prefix hfp (inpVec_length x) haddbw, ← hsz_eq]; exact hgt)
      · rw [decide_eq_false hgt]; symm; exact decide_eq_false (by rw [bitsVal_prefix hfp (inpVec_length x) haddbw, ← hsz_eq]; exact hgt)

private def extVal {V : Type} [Fintype V] {a : ℕ} (x : V → Bool) (y : Fin a → Bool) (w : ℕ) : Bool :=
  if h0 : w = 0 then false
  else if h1' : w = 1 then true
  else if h1 : w < 2 + Fintype.card V then x ((Fintype.equivFin V).symm ⟨w - 2, by omega⟩)
  else if h2 : w < 2 + Fintype.card V + a then y ⟨w - (2 + Fintype.card V), by omega⟩
  else false

private def litOfWire {V : Type} [Fintype V] [DecidableEq V] {a : ℕ} (w : ℕ) (sgn : Bool) :
    Option (Literal (V ⊕ Fin a)) :=
  if h0 : w < 2 then none
  else if h1 : w < 2 + Fintype.card V then
    some (Sum.inl ((Fintype.equivFin V).symm ⟨w - 2, by omega⟩), sgn)
  else if h2 : w < 2 + Fintype.card V + a then
    some (Sum.inr ⟨w - (2 + Fintype.card V), by omega⟩, sgn)
  else none

private def isTautWire (p : ℕ × Bool) : Bool :=
  (p.1 == 0 && p.2 == false) || (p.1 == 1 && p.2 == true)

private def clausesFromWires {V : Type} [Fintype V] [DecidableEq V] (a : ℕ)
    (lits : List (ℕ × Bool)) : Finset (Clause (V ⊕ Fin a)) :=
  if lits.any isTautWire then ∅
  else {(lits.filterMap (fun p => litOfWire (V := V) (a := a) p.1 p.2)).toFinset}

private lemma clausesFromWires_card_le {V : Type} [Fintype V] [DecidableEq V] (a : ℕ)
    (lits : List (ℕ × Bool)) :
    (clausesFromWires (V := V) a lits).card ≤ 1 := by
  unfold clausesFromWires
  split_ifs <;> simp

private lemma clausesFromWires_width {V : Type} [Fintype V] [DecidableEq V] (a : ℕ)
    (lits : List (ℕ × Bool)) :
    ∀ cl ∈ clausesFromWires (V := V) a lits, cl.card ≤ lits.length := by
  intro cl hcl
  unfold clausesFromWires at hcl
  split_ifs at hcl with ht
  · simp at hcl
  · simp only [Finset.mem_singleton] at hcl
    subst hcl
    exact le_trans (List.toFinset_card_le _) (List.length_filterMap_le _ _)

private lemma clausesFromWires_sat_iff {V : Type} [Fintype V] [DecidableEq V] {a : ℕ}
    (x : V → Bool) (y : Fin a → Bool) (lits : List (ℕ × Bool))
    (hlt : ∀ p ∈ lits, p.1 < 2 + Fintype.card V + a) :
    (∀ cl ∈ clausesFromWires (V := V) a lits, ClauseSat (Sum.elim x y) cl) ↔
      ∃ p ∈ lits, extVal x y p.1 = p.2 := by
  unfold clausesFromWires
  by_cases ht : lits.any isTautWire = true
  · simp only [ht, ↓reduceIte, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_iff]
    rw [List.any_eq_true] at ht
    obtain ⟨⟨w, s⟩, hmem, htw⟩ := ht
    refine ⟨(w, s), hmem, ?_⟩
    simp only [isTautWire, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at htw
    rcases htw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [extVal]
  · simp only [ht, Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton, forall_eq]
    unfold ClauseSat
    simp only [List.mem_toFinset, List.mem_filterMap]
    constructor
    · rintro ⟨l, ⟨⟨w, s⟩, hmem, hlw⟩, hsat⟩
      refine ⟨(w, s), hmem, ?_⟩
      unfold litOfWire at hlw
      by_cases h0 : w < 2
      · simp [h0] at hlw
      · by_cases h1 : w < 2 + Fintype.card V
        · simp only [h0, h1, ↓reduceDIte, Option.some.injEq] at hlw
          subst hlw
          have hw0 : w ≠ 0 := by omega
          have hw1 : w ≠ 1 := by omega
          simpa [extVal, hw0, hw1, h1] using hsat
        · by_cases h2 : w < 2 + Fintype.card V + a
          · simp only [h0, h1, h2, ↓reduceDIte, Option.some.injEq] at hlw
            subst hlw
            have hw0 : w ≠ 0 := by omega
            have hw1 : w ≠ 1 := by omega
            simpa [extVal, hw0, hw1, h1, h2] using hsat
          · simp [h0, h1, h2] at hlw
    · rintro ⟨⟨w, s⟩, hmem, heq⟩
      have hnt : isTautWire (w, s) = false := by
        by_contra h1
        have h1' : isTautWire (w, s) = true := Bool.eq_true_of_not_eq_false h1
        exact ht (List.any_eq_true.mpr ⟨(w, s), hmem, h1'⟩)
      have hw_ge2 : ¬ (w < 2) := by
        intro hw2
        have : w = 0 ∨ w = 1 := by omega
        rcases this with rfl | rfl
        · simp [extVal] at heq; subst heq; simp [isTautWire] at hnt
        · simp [extVal] at heq; subst heq; simp [isTautWire] at hnt
      have hw_lt : w < 2 + Fintype.card V + a := hlt (w, s) hmem
      by_cases h1 : w < 2 + Fintype.card V
      · refine ⟨(Sum.inl ((Fintype.equivFin V).symm ⟨w - 2, by omega⟩), s),
          ⟨(w, s), hmem, by simp [litOfWire, hw_ge2, h1]⟩, ?_⟩
        have hw0 : w ≠ 0 := by omega
        have hw1 : w ≠ 1 := by omega
        simpa [extVal, hw0, hw1, h1] using heq
      · refine ⟨(Sum.inr ⟨w - (2 + Fintype.card V), by omega⟩, s),
          ⟨(w, s), hmem, by simp [litOfWire, hw_ge2, h1, hw_lt]⟩, ?_⟩
        have hw0 : w ≠ 0 := by omega
        have hw1 : w ≠ 1 := by omega
        simpa [extVal, hw0, hw1, h1, hw_lt] using heq

private def gateTseitin {V : Type} [Fintype V] [DecidableEq V] (gs : List Gate)
    (i : Fin gs.length) : Finset (Clause (V ⊕ Fin gs.length)) :=
  let g := gs[i]
  let wi := 2 + Fintype.card V + i.val
  let u := g.inputs.getD 0 0
  let v := g.inputs.getD 1 0
  match g.op with
  | .and =>
    clausesFromWires gs.length [(wi, false), (u, true)] ∪
    clausesFromWires gs.length [(wi, false), (v, true)] ∪
    clausesFromWires gs.length [(wi, true), (u, false), (v, false)]
  | .or =>
    clausesFromWires gs.length [(wi, true), (u, false)] ∪
    clausesFromWires gs.length [(wi, true), (v, false)] ∪
    clausesFromWires gs.length [(wi, false), (u, true), (v, true)]
  | .not =>
    clausesFromWires gs.length [(wi, true), (u, true)] ∪
    clausesFromWires gs.length [(wi, false), (u, false)]
  | _ => ∅

private def tseitinAll {V : Type} [Fintype V] [DecidableEq V] (gs : List Gate) :
    Finset (Clause (V ⊕ Fin gs.length)) :=
  Finset.univ.biUnion (gateTseitin (V := V) gs)

private lemma tseitinAll_card_le {V : Type} [Fintype V] [DecidableEq V] (gs : List Gate) :
    (tseitinAll (V := V) gs).card ≤ 3 * gs.length := by
  calc (tseitinAll (V := V) gs).card
      ≤ ∑ i : Fin gs.length, (gateTseitin (V := V) gs i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin gs.length, 3 := by
        apply Finset.sum_le_sum
        intro i _
        unfold gateTseitin; dsimp only
        cases gs[i].op
        · calc _ ≤ (clausesFromWires gs.length _ ∪ clausesFromWires gs.length _).card +
                  (clausesFromWires gs.length _).card := Finset.card_union_le _ _
            _ ≤ (clausesFromWires gs.length _).card + (clausesFromWires gs.length _).card +
                  (clausesFromWires gs.length _).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
            _ ≤ 1 + 1 + 1 := by
                have h1 := clausesFromWires_card_le (V := V) gs.length [(2 + Fintype.card V + i.val, false), (gs[i].inputs.getD 0 0, true)]
                have h2 := clausesFromWires_card_le (V := V) gs.length [(2 + Fintype.card V + i.val, false), (gs[i].inputs.getD 1 0, true)]
                have h3 := clausesFromWires_card_le (V := V) gs.length [(2 + Fintype.card V + i.val, true), (gs[i].inputs.getD 0 0, false), (gs[i].inputs.getD 1 0, false)]
                omega
        · calc _ ≤ (clausesFromWires gs.length _ ∪ clausesFromWires gs.length _).card +
                  (clausesFromWires gs.length _).card := Finset.card_union_le _ _
            _ ≤ (clausesFromWires gs.length _).card + (clausesFromWires gs.length _).card +
                  (clausesFromWires gs.length _).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
            _ ≤ 1 + 1 + 1 := by
                have h1 := clausesFromWires_card_le (V := V) gs.length [(2 + Fintype.card V + i.val, true), (gs[i].inputs.getD 0 0, false)]
                have h2 := clausesFromWires_card_le (V := V) gs.length [(2 + Fintype.card V + i.val, true), (gs[i].inputs.getD 1 0, false)]
                have h3 := clausesFromWires_card_le (V := V) gs.length [(2 + Fintype.card V + i.val, false), (gs[i].inputs.getD 0 0, true), (gs[i].inputs.getD 1 0, true)]
                omega
        · calc _ ≤ (clausesFromWires gs.length _).card + (clausesFromWires gs.length _).card :=
                  Finset.card_union_le _ _
            _ ≤ 3 := by
                have h1 := clausesFromWires_card_le (V := V) gs.length [(2 + Fintype.card V + i.val, true), (gs[i].inputs.getD 0 0, true)]
                have h2 := clausesFromWires_card_le (V := V) gs.length [(2 + Fintype.card V + i.val, false), (gs[i].inputs.getD 0 0, false)]
                omega
        · simp
        · simp
    _ = 3 * gs.length := by simp [mul_comm]

private lemma tseitinAll_width {V : Type} [Fintype V] [DecidableEq V] (gs : List Gate) :
    ∀ cl ∈ tseitinAll (V := V) gs, cl.card ≤ 3 := by
  intro cl hcl
  simp only [tseitinAll, Finset.mem_biUnion, Finset.mem_univ, true_and] at hcl
  obtain ⟨i, hi⟩ := hcl
  unfold gateTseitin at hi; dsimp only at hi
  cases hop : gs[i].op <;> rw [hop] at hi
  · simp only [Finset.mem_union] at hi
    rcases hi with (h | h) | h
    · exact (clausesFromWires_width _ _ cl h).trans (by simp)
    · exact (clausesFromWires_width _ _ cl h).trans (by simp)
    · exact (clausesFromWires_width _ _ cl h).trans (by simp)
  · simp only [Finset.mem_union] at hi
    rcases hi with (h | h) | h
    · exact (clausesFromWires_width _ _ cl h).trans (by simp)
    · exact (clausesFromWires_width _ _ cl h).trans (by simp)
    · exact (clausesFromWires_width _ _ cl h).trans (by simp)
  · simp only [Finset.mem_union] at hi
    rcases hi with h | h
    · exact (clausesFromWires_width _ _ cl h).trans (by simp)
    · exact (clausesFromWires_width _ _ cl h).trans (by simp)
  · simp at hi
  · simp at hi

private lemma gate_eval_at {V : Type} [Fintype V] {gs : List Gate}
    (hv : CValid (2 + Fintype.card V) gs) (x : V → Bool) (i : Fin gs.length) :
    wVal gs (inpVec x) (2 + Fintype.card V + i.val) =
      gs[i].op.eval (gs[i].inputs.map (wVal gs (inpVec x))) := by
  have hsplit : gs = gs.take i.val ++ [gs[i]] ++ gs.drop (i.val + 1) := by
    have h1 := List.take_append_drop i.val gs
    have h2 : gs.drop i.val = gs[i] :: gs.drop (i.val + 1) := List.drop_eq_getElem_cons i.isLt
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  have hpref : gs.take i.val ++ [gs[i]] <+: gs := ⟨gs.drop (i.val + 1), hsplit.symm⟩
  have hlen_t : (gs.take i.val).length = i.val := List.length_take_of_le (le_of_lt i.isLt)
  have hlt1 : 2 + Fintype.card V + i.val < 2 + Fintype.card V + (gs.take i.val ++ [gs[i]]).length := by
    simp [hlen_t]
  rw [wVal_prefix hpref (inpVec_length x) hlt1]
  have heq_w : 2 + Fintype.card V + i.val = 2 + Fintype.card V + (gs.take i.val).length := by
    rw [hlen_t]
  rw [heq_w, wVal_push (gs.take i.val) gs[i] (inpVec x) (inpVec_length x)]
  congr 1
  apply List.map_congr_left
  intro w hw
  have hrb : w < 2 + Fintype.card V + i.val := by
    have h := hv.1 i.val i.isLt w
    unfold gateAt at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt] at h
    exact h hw
  have hpref0 : gs.take i.val <+: gs := List.take_prefix i.val gs
  rw [wVal_prefix hpref0 (inpVec_length x) (by rw [hlen_t]; exact hrb)]

private lemma satisfies_tseitinAll_iff {V : Type} [Fintype V] [DecidableEq V] {gs : List Gate}
    (hv : CValid (2 + Fintype.card V) gs) (x : V → Bool) (y : Fin gs.length → Bool) :
    Satisfies (Sum.elim x y) (↑(tseitinAll (V := V) gs) : Set (Clause (V ⊕ Fin gs.length))) ↔
      y = fun i => wVal gs (inpVec x) (2 + Fintype.card V + i.val) := by
  have hgate_iff : ∀ i : Fin gs.length,
      (∀ cl ∈ gateTseitin (V := V) gs i, ClauseSat (Sum.elim x y) cl) ↔
        y i = gs[i].op.eval (gs[i].inputs.map (extVal x y)) := by
    intro i
    have hok := hv.2 gs[i] (List.getElem_mem i.isLt)
    have hrb : ∀ w ∈ gs[i].inputs, w < 2 + Fintype.card V + gs.length := fun w hw => by
      have h := hv.1 i.val i.isLt w
      unfold gateAt at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt] at h
      have := h hw; omega
    have hext_i : extVal x y (2 + Fintype.card V + i.val) = y i := by
      unfold extVal
      have h0 : 2 + Fintype.card V + i.val ≠ 0 := by omega
      have h1 : 2 + Fintype.card V + i.val ≠ 1 := by omega
      have h2 : ¬ (2 + Fintype.card V + i.val < 2 + Fintype.card V) := by omega
      have h3 : 2 + Fintype.card V + i.val < 2 + Fintype.card V + gs.length := by omega
      simp [h0, h1, h2, h3]
    unfold gateTseitin; dsimp only
    rcases hok with ⟨hop | hop, hlen2⟩ | ⟨hop, hlen1⟩
    · rw [hop]
      rcases List.length_eq_two.mp hlen2 with ⟨u, v, hg⟩
      have hu : u < 2 + Fintype.card V + gs.length := hrb u (by rw [hg]; simp)
      have hv' : v < 2 + Fintype.card V + gs.length := hrb v (by rw [hg]; simp)
      rw [hg]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Finset.mem_union,
        List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      have h1 := clausesFromWires_sat_iff (V := V) x y
        [(2 + Fintype.card V + i.val, false), (u, true)]
        (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> dsimp only <;> omega)
      have h2 := clausesFromWires_sat_iff (V := V) x y
        [(2 + Fintype.card V + i.val, false), (v, true)]
        (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> dsimp only <;> omega)
      have h3 := clausesFromWires_sat_iff (V := V) x y
        [(2 + Fintype.card V + i.val, true), (u, false), (v, false)]
        (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega)
      have hall : (∀ cl, (cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, false), (u, true)] ∨
          cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, false), (v, true)]) ∨
          cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, true), (u, false), (v, false)] →
          ClauseSat (Sum.elim x y) cl) ↔
          ((∀ cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, false), (u, true)], ClauseSat (Sum.elim x y) cl) ∧
           (∀ cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, false), (v, true)], ClauseSat (Sum.elim x y) cl) ∧
           (∀ cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, true), (u, false), (v, false)], ClauseSat (Sum.elim x y) cl)) :=
        ⟨fun h => ⟨fun c hc => h c (Or.inl (Or.inl hc)), fun c hc => h c (Or.inl (Or.inr hc)), fun c hc => h c (Or.inr hc)⟩,
         fun ⟨ha, hb, hc⟩ c h => by rcases h with (h | h) | h; exact ha c h; exact hb c h; exact hc c h⟩
      rw [hall, h1, h2, h3]
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, hext_i]
      cases y i <;> cases extVal x y u <;> cases extVal x y v <;> decide
    · rw [hop]
      rcases List.length_eq_two.mp hlen2 with ⟨u, v, hg⟩
      have hu : u < 2 + Fintype.card V + gs.length := hrb u (by rw [hg]; simp)
      have hv' : v < 2 + Fintype.card V + gs.length := hrb v (by rw [hg]; simp)
      rw [hg]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Finset.mem_union,
        List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have h1 := clausesFromWires_sat_iff (V := V) x y
        [(2 + Fintype.card V + i.val, true), (u, false)]
        (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> dsimp only <;> omega)
      have h2 := clausesFromWires_sat_iff (V := V) x y
        [(2 + Fintype.card V + i.val, true), (v, false)]
        (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> dsimp only <;> omega)
      have h3 := clausesFromWires_sat_iff (V := V) x y
        [(2 + Fintype.card V + i.val, false), (u, true), (v, true)]
        (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega)
      have hall : (∀ cl, (cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, true), (u, false)] ∨
          cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, true), (v, false)]) ∨
          cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, false), (u, true), (v, true)] →
          ClauseSat (Sum.elim x y) cl) ↔
          ((∀ cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, true), (u, false)], ClauseSat (Sum.elim x y) cl) ∧
           (∀ cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, true), (v, false)], ClauseSat (Sum.elim x y) cl) ∧
           (∀ cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, false), (u, true), (v, true)], ClauseSat (Sum.elim x y) cl)) :=
        ⟨fun h => ⟨fun c hc => h c (Or.inl (Or.inl hc)), fun c hc => h c (Or.inl (Or.inr hc)), fun c hc => h c (Or.inr hc)⟩,
         fun ⟨ha, hb, hc⟩ c h => by rcases h with (h | h) | h; exact ha c h; exact hb c h; exact hc c h⟩
      rw [hall, h1, h2, h3]
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, hext_i]
      cases y i <;> cases extVal x y u <;> cases extVal x y v <;> decide
    · rw [hop]
      rcases List.length_eq_one_iff.mp hlen1 with ⟨u, hg⟩
      have hu : u < 2 + Fintype.card V + gs.length := hrb u (by rw [hg]; simp)
      rw [hg]
      simp only [List.getD_cons_zero, Finset.mem_union,
        List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
      have h1 := clausesFromWires_sat_iff (V := V) x y
        [(2 + Fintype.card V + i.val, true), (u, true)]
        (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> dsimp only <;> omega)
      have h2 := clausesFromWires_sat_iff (V := V) x y
        [(2 + Fintype.card V + i.val, false), (u, false)]
        (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> dsimp only <;> omega)
      have hall : (∀ cl, cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, true), (u, true)] ∨
          cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, false), (u, false)] →
          ClauseSat (Sum.elim x y) cl) ↔
          ((∀ cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, true), (u, true)], ClauseSat (Sum.elim x y) cl) ∧
           (∀ cl ∈ clausesFromWires gs.length [(2 + Fintype.card V + i.val, false), (u, false)], ClauseSat (Sum.elim x y) cl)) :=
        ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
         fun ⟨ha, hb⟩ c h => by rcases h with h | h; exact ha c h; exact hb c h⟩
      rw [hall, h1, h2]
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, hext_i]
      cases y i <;> cases extVal x y u <;> decide
  have hsat_iff : Satisfies (Sum.elim x y) (↑(tseitinAll (V := V) gs) : Set (Clause (V ⊕ Fin gs.length))) ↔
      ∀ i : Fin gs.length, y i = gs[i].op.eval (gs[i].inputs.map (extVal x y)) := by
    unfold Satisfies
    simp only [Finset.mem_coe, tseitinAll, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro h i; exact (hgate_iff i).mp (fun cl hcl => h cl ⟨i, hcl⟩)
    · rintro h cl ⟨i, hcl⟩; exact (hgate_iff i).mpr (h i) cl hcl
  rw [hsat_iff]
  have hext_inp : ∀ w < 2 + Fintype.card V, extVal x y w = wVal gs (inpVec x) w := by
    intro w hw
    rw [wVal_input gs (inpVec x) (by rw [inpVec_length]; exact hw)]
    unfold extVal
    by_cases h0 : w = 0
    · subst h0; simp only [↓reduceDIte, inpVec_zero]
    · by_cases h1 : w = 1
      · subst h1; simp only [Nat.one_ne_zero, ↓reduceDIte, inpVec_one]
      · simp only [h0, h1, ↓reduceDIte, hw]
        have hlt : w - 2 < Fintype.card V := by omega
        unfold inpVec
        have hw2 : w = (w - 2) + 2 := by omega
        conv_rhs => rw [hw2]
        simp [List.getD_eq_getElem?_getD, hlt]
  constructor
  · intro h
    funext i
    rcases i with ⟨iv, hiv⟩
    induction iv using Nat.strong_induction_on with
    | ind iv ih =>
      rw [h ⟨iv, hiv⟩, gate_eval_at hv x ⟨iv, hiv⟩]
      congr 1
      apply List.map_congr_left
      intro w hw
      have hrb : w < 2 + Fintype.card V + iv := by
        have h' := hv.1 iv hiv w
        unfold gateAt at h'
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiv] at h'
        exact h' hw
      by_cases hw0 : w < 2 + Fintype.card V
      · exact hext_inp w hw0
      · have hidx : w - (2 + Fintype.card V) < iv := by omega
        have hlt : w < 2 + Fintype.card V + gs.length := by omega
        have heq : extVal x y w = y ⟨w - (2 + Fintype.card V), by omega⟩ := by
          unfold extVal
          have h0 : w ≠ 0 := by omega
          have h1 : w ≠ 1 := by omega
          simp [h0, h1, hw0, hlt]
        rw [heq, ih (w - (2 + Fintype.card V)) hidx (by omega)]
        dsimp only; congr 1; omega
  · rintro rfl i
    dsimp only
    rw [gate_eval_at hv x i]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hrb : w < 2 + Fintype.card V + gs.length := by
      have h' := hv.1 i.val i.isLt w
      unfold gateAt at h'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt] at h'
      have := h' hw; omega
    by_cases hw0 : w < 2 + Fintype.card V
    · exact (hext_inp w hw0).symm
    · unfold extVal
      have h0 : w ≠ 0 := by omega
      have h1 : w ≠ 1 := by omega
      simp only [h0, h1, ↓reduceDIte, hw0, hrb]
      congr 1; omega

private def varOfFlag {V : Type} [Fintype V] {a : ℕ} (w : ℕ) (h : w < 2 + Fintype.card V + a)
    (hge : 2 + Fintype.card V ≤ w) : V ⊕ Fin a :=
  Sum.inr ⟨w - (2 + Fintype.card V), by omega⟩

private def varOfWire {V : Type} [Fintype V] (a : ℕ) (w : ℕ) : Option (V ⊕ Fin a) :=
  if hge : 2 + Fintype.card V ≤ w then
    if hlt : w < 2 + Fintype.card V + a then
      some (Sum.inr ⟨w - (2 + Fintype.card V), by omega⟩)
    else none
  else none

private def flagVar {V : Type} [Fintype V] {a : ℕ} (ha : 0 < a) (w : ℕ) : V ⊕ Fin a :=
  if h : w - (2 + Fintype.card V) < a then Sum.inr ⟨w - (2 + Fintype.card V), h⟩
  else Sum.inr ⟨0, ha⟩

private lemma flagVar_ne_inl {V : Type} [Fintype V] {a : ℕ} (ha : 0 < a) (w : ℕ) (v : V) :
    flagVar ha w ≠ Sum.inl v := by
  unfold flagVar
  split_ifs <;> simp

private lemma flagVar_inj {V : Type} [Fintype V] {a : ℕ} (ha : 0 < a) {w1 w2 : ℕ}
    (h1l : 2 + Fintype.card V ≤ w1) (h1u : w1 < 2 + Fintype.card V + a)
    (h2l : 2 + Fintype.card V ≤ w2) (h2u : w2 < 2 + Fintype.card V + a)
    (hne : w1 ≠ w2) : flagVar (V := V) ha w1 ≠ flagVar (V := V) ha w2 := by
  unfold flagVar
  have h1 : w1 - (2 + Fintype.card V) < a := by omega
  have h2 : w2 - (2 + Fintype.card V) < a := by omega
  simp only [h1, h2, ↓reduceDIte, ne_eq, Sum.inr.injEq, Fin.mk.injEq]
  omega

private lemma eval_flagVar {V : Type} [Fintype V] {gs : List Gate} (ha : 0 < gs.length)
    (x : V → Bool) {w : ℕ} (hl : 2 + Fintype.card V ≤ w)
    (hu : w < 2 + Fintype.card V + gs.length) :
    Sum.elim x (fun i : Fin gs.length => wVal gs (inpVec x) (2 + Fintype.card V + i.val))
      (flagVar ha w) = wVal gs (inpVec x) w := by
  unfold flagVar
  have hlt : w - (2 + Fintype.card V) < gs.length := by omega
  simp only [hlt, ↓reduceDIte, Sum.elim_inr]
  congr 1; omega

private def pClauses {n : ℕ} {G : BipGraph (n + 1) n} {a : ℕ} (ha : 0 < a) :
    BuiltP n G → Finset (Clause (GEdge G ⊕ Fin a))
  | .leaf p _ f =>
    ((pigeonEdges G p).map (fun e => ({(flagVar ha f, false), (Sum.inl e, false)} : Clause (GEdge G ⊕ Fin a)))).toFinset
  | .node l r _ f _ =>
    pClauses ha l ∪ pClauses ha r ∪
      {({(flagVar ha f, false), (flagVar ha l.flag, true), (flagVar ha r.flag, true)} : Clause (GEdge G ⊕ Fin a))}

private lemma pClauses_width {n : ℕ} {G : BipGraph (n + 1) n} {a : ℕ} (ha : 0 < a)
    (t : BuiltP n G) : ∀ cl ∈ pClauses ha t, cl.card ≤ 3 := by
  induction t with
  | leaf p bs f =>
    intro cl hcl
    simp only [pClauses, List.mem_toFinset, List.mem_map] at hcl
    rcases hcl with ⟨e, _, rfl⟩
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  | node l r bs f sz ihl ihr =>
    intro cl hcl
    simp only [pClauses, Finset.mem_union, Finset.mem_singleton] at hcl
    rcases hcl with (h | h) | rfl
    · exact ihl cl h
    · exact ihr cl h
    · exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))

private def BuiltP.leafCount {n : ℕ} {G : BipGraph (n + 1) n} : BuiltP n G → ℕ
  | .leaf _ _ _ => 1
  | .node l r _ _ _ => l.leafCount + r.leafCount

private lemma buildP_leafCount {n w0 : ℕ} (G : BipGraph (n + 1) n)
    (t : BTree (Fin (n + 1))) (gs : List Gate) :
    (buildP G w0 gs t).2.leafCount = t.size := by
  induction t generalizing gs with
  | leaf _ => rfl
  | node l r ihl ihr =>
    unfold buildP
    simp only [BuiltP.leafCount, BTree.size, ihl, ihr]

private lemma BuiltP.leafCount_pos {n : ℕ} {G : BipGraph (n + 1) n} (t : BuiltP n G) :
    1 ≤ t.leafCount := by
  induction t with
  | leaf _ _ _ => simp [BuiltP.leafCount]
  | node l r _ _ _ ihl ihr => simp [BuiltP.leafCount]; omega

private lemma pClauses_card_le {n b : ℕ} {G : BipGraph (n + 1) n} (hLd : LeftDegLe G b)
    {a : ℕ} (ha : 0 < a) (t : BuiltP n G) :
    (pClauses ha t).card + 1 ≤ (b + 1) * t.leafCount := by
  induction t with
  | leaf p bs f =>
    simp only [pClauses, BuiltP.leafCount, mul_one]
    have h1 : (((pigeonEdges G p).map (fun e => ({(flagVar ha f, false), (Sum.inl e, false)} :
        Clause (GEdge G ⊕ Fin a)))).toFinset).card ≤ (G p).card := by
      calc _ ≤ ((pigeonEdges G p).map _).length := List.toFinset_card_le _
        _ = (G p).card := by simp [pigeonEdges_length]
    have h2 := hLd p
    omega
  | node l r bs f sz ihl ihr =>
    simp only [pClauses, BuiltP.leafCount]
    have h1 := Finset.card_union_le (pClauses ha l ∪ pClauses ha r)
      {({(flagVar ha f, false), (flagVar ha l.flag, true), (flagVar ha r.flag, true)} : Clause (GEdge G ⊕ Fin a))}
    have h2 := Finset.card_union_le (pClauses ha l) (pClauses ha r)
    have h3 : ({({(flagVar ha f, false), (flagVar ha l.flag, true), (flagVar ha r.flag, true)} : Clause (GEdge G ⊕ Fin a))} :
        Finset (Clause (GEdge G ⊕ Fin a))).card = 1 := Finset.card_singleton _
    nlinarith

private lemma pClauses_sat {n b w0 : ℕ} {G : BipGraph (n + 1) n}
    (hLd : LeftDegLe G b) (hw0 : b < 2 ^ w0) (hw0_pos : 1 ≤ w0)
    (bt : BTree (Fin (n + 1))) (gs0 gs : List Gate)
    (hv0 : CValid (2 + Fintype.card (GEdge G)) gs0)
    (hpref : (buildP G w0 gs0 bt).1 <+: gs)
    (ha : 0 < gs.length) (x : GEdge G → Bool) :
    Satisfies (Sum.elim x (fun i : Fin gs.length => wVal gs (inpVec x) (2 + Fintype.card (GEdge G) + i.val)))
      (↑(pClauses ha (buildP G w0 gs0 bt).2) : Set (Clause (GEdge G ⊕ Fin gs.length))) := by
  induction bt generalizing gs0 with
  | leaf p =>
    intro cl hcl
    simp only [Finset.mem_coe, buildP, pClauses, List.mem_toFinset, List.mem_map] at hcl
    rcases hcl with ⟨e, he, rfl⟩
    have hsp := buildP_spec G hLd hw0 hw0_pos (.leaf p) gs0 hv0
    have hwf := BuiltP.wf_mono (List.IsPrefix.length_le hpref) hsp.2.2.2.2.2.1
    set r1 := mkSumList (2 + Fintype.card (GEdge G)) w0 gs0 ((pigeonEdges G p).map edgeWire) with hr1
    set r2 := mkLtConst (2 + Fintype.card (GEdge G)) r1.1 r1.2 1 with hr2
    have hwf_f : 2 + Fintype.card (GEdge G) ≤ r2.2 ∧ r2.2 < 2 + Fintype.card (GEdge G) + gs.length :=
      ⟨hwf.2.1, hwf.2.2⟩
    have hfl_val : wVal gs (inpVec x) r2.2 = decide ((pigeonEdges G p).countP (fun e => x e) < 1) := by
      rw [wVal_prefix hpref (inpVec_length x) hsp.2.2.2.2.2.1.2.2]
      have hx := hsp.2.2.2.2.2.2.2 x
      have hx1 : bitsVal r2.1 (inpVec x) r1.2 = (pigeonEdges G p).countP (fun e => x e) := by
        simpa [buildP, BuiltP.bits, BTree.leaves] using hx.1
      have hx2 : wVal r2.1 (inpVec x) r2.2 = decide (bitsVal r2.1 (inpVec x) r1.2 < 1) := hx.2
      change wVal r2.1 (inpVec x) r2.2 = _
      rw [hx2]
      by_cases hlt : bitsVal r2.1 (inpVec x) r1.2 < 1
      · rw [decide_eq_true hlt]; symm; exact decide_eq_true (by rwa [← hx1])
      · rw [decide_eq_false hlt]; symm; exact decide_eq_false (by rwa [← hx1])
    by_cases hxe : x e = false
    · refine ⟨(Sum.inl e, false), by simp, ?_⟩
      simpa using hxe
    · refine ⟨(flagVar ha r2.2, false), by simp, ?_⟩
      rw [eval_flagVar ha x hwf_f.1 hwf_f.2, hfl_val]
      have hxe' : x e = true := by cases h : x e <;> simp_all
      have hpos : 0 < (pigeonEdges G p).countP (fun e => x e) :=
        List.countP_pos_iff.mpr ⟨e, he, hxe'⟩
      exact decide_eq_false (by omega)
  | node l r ihl ihr =>
    have hsp := buildP_spec G hLd hw0 hw0_pos (.node l r) gs0 hv0
    have hspl := buildP_spec G hLd hw0 hw0_pos l gs0 hv0
    set rl := buildP G w0 gs0 l
    have hspr := buildP_spec G hLd hw0 hw0_pos r rl.1 hspl.1
    set rr := buildP G w0 rl.1 r
    have hpref_r : rr.1 <+: (buildP G w0 gs0 (.node l r)).1 := by
      unfold buildP
      set k := max rl.2.bits.length rr.2.bits.length
      set radd := mkAddBits (2 + Fintype.card (GEdge G)) rr.1 k rl.2.bits rr.2.bits
      have hm : 2 ≤ 2 + Fintype.card (GEdge G) := by omega
      have hlb : ∀ w ∈ rl.2.bits, w < 2 + Fintype.card (GEdge G) + rr.1.length := fun w hw => by
        have h1 : w < 2 + Fintype.card (GEdge G) + rl.1.length := by
          cases hlt : rl.2 with
          | leaf _ _ _ => have := hspl.2.2.2.2.2.1; rw [hlt] at this; exact this.1 w (by simpa [hlt, BuiltP.bits] using hw)
          | node _ _ _ _ _ => have := hspl.2.2.2.2.2.1; rw [hlt] at this; exact this.2.2.1 w (by simpa [hlt, BuiltP.bits] using hw)
        have h2 := List.IsPrefix.length_le hspr.2.1; omega
      have hrb : ∀ w ∈ rr.2.bits, w < 2 + Fintype.card (GEdge G) + rr.1.length := fun w hw => by
        cases hrt : rr.2 with
        | leaf _ _ _ => have := hspr.2.2.2.2.2.1; rw [hrt] at this; exact this.1 w (by simpa [hrt, BuiltP.bits] using hw)
        | node _ _ _ _ _ => have := hspr.2.2.2.2.2.1; rw [hrt] at this; exact this.2.2.1 w (by simpa [hrt, BuiltP.bits] using hw)
      have hadd := mkAddBits_spec hm hspr.1 (le_max_left _ _) (le_max_right _ _) hlb hrb
      have hfl := mkLtConst_spec hm hadd.1 hadd.2.2.2.2.1 (K := rl.2.sz + rr.2.sz) (by
        rw [hadd.2.2.2.1, hspl.2.2.2.2.1, hspr.2.2.2.2.1]
        have h1 := l.size_le_pow_height
        have h2 := r.size_le_pow_height
        have hkl : max rl.2.bits.length rr.2.bits.length = w0 + max l.height r.height := by
          rw [hspl.2.2.2.1, hspr.2.2.2.1]; omega
        rw [hkl]
        have hm1 : 2 ^ l.height ≤ 2 ^ max l.height r.height := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
        have hm2 : 2 ^ r.height ≤ 2 ^ max l.height r.height := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
        have hw2 : 2 ≤ 2 ^ w0 := by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hw0_pos
        have hpow : 2 ^ (w0 + max l.height r.height + 1) = 2 ^ w0 * (2 * 2 ^ max l.height r.height) := by
          rw [pow_succ', pow_add]; ring
        rw [hpow]; nlinarith [Nat.two_pow_pos (max l.height r.height)])
      exact hadd.2.1.trans hfl.2.1
    have hpref_l : rl.1 <+: gs := hspr.2.1.trans (hpref_r.trans hpref)
    have hpref_r' : rr.1 <+: gs := hpref_r.trans hpref
    intro cl hcl
    simp only [Finset.mem_coe, buildP, pClauses, Finset.mem_union, Finset.mem_singleton] at hcl
    rcases hcl with (h | h) | rfl
    · exact ihl gs0 hv0 hpref_l cl (by simpa using h)
    · exact ihr rl.1 hspl.1 hpref_r' cl (by simpa using h)
    · have hwf_n := hsp.2.2.2.2.2.1
      have hwf_l := hspl.2.2.2.2.2.1
      have hwf_r := hspr.2.2.2.2.2.1
      have hfl_n_lt : (buildP G w0 gs0 (.node l r)).2.flag < 2 + Fintype.card (GEdge G) + (buildP G w0 gs0 (.node l r)).1.length := by
        exact hwf_n.2.2.2.2.1
      have hfl_n_ge : 2 + Fintype.card (GEdge G) ≤ (buildP G w0 gs0 (.node l r)).2.flag := hwf_n.2.2.2.1
      have hfl_l_lt : rl.2.flag < 2 + Fintype.card (GEdge G) + rl.1.length := by
        cases h : rl.2 <;> rw [h] at hwf_l <;> first | exact hwf_l.2.2 | exact hwf_l.2.2.2.2.1
      have hfl_l_ge : 2 + Fintype.card (GEdge G) ≤ rl.2.flag := by
        cases h : rl.2 <;> rw [h] at hwf_l <;> first | exact hwf_l.2.1 | exact hwf_l.2.2.2.1
      have hfl_r_lt : rr.2.flag < 2 + Fintype.card (GEdge G) + rr.1.length := by
        cases h : rr.2 <;> rw [h] at hwf_r <;> first | exact hwf_r.2.2 | exact hwf_r.2.2.2.2.1
      have hfl_r_ge : 2 + Fintype.card (GEdge G) ≤ rr.2.flag := by
        cases h : rr.2 <;> rw [h] at hwf_r <;> first | exact hwf_r.2.1 | exact hwf_r.2.2.2.1
      have hlen_n := List.IsPrefix.length_le hpref
      have hlen_l := List.IsPrefix.length_le hpref_l
      have hlen_r := List.IsPrefix.length_le hpref_r'
      have hvn : wVal gs (inpVec x) (buildP G w0 gs0 (.node l r)).2.flag =
          decide ((l.leaves.map (fun p => (pigeonEdges G p).countP (fun e => x e))).sum +
                  (r.leaves.map (fun p => (pigeonEdges G p).countP (fun e => x e))).sum < l.size + r.size) := by
        rw [wVal_prefix hpref (inpVec_length x) hfl_n_lt]
        have hx := hsp.2.2.2.2.2.2.2 x
        simpa [BTree.leaves, List.map_append, List.sum_append, BTree.size, hx.1] using hx.2
      have hvl : wVal gs (inpVec x) rl.2.flag =
          decide ((l.leaves.map (fun p => (pigeonEdges G p).countP (fun e => x e))).sum < l.size) := by
        rw [wVal_prefix hpref_l (inpVec_length x) hfl_l_lt]
        have hx := hspl.2.2.2.2.2.2.2 x
        simpa [hx.1] using hx.2
      have hvr : wVal gs (inpVec x) rr.2.flag =
          decide ((r.leaves.map (fun p => (pigeonEdges G p).countP (fun e => x e))).sum < r.size) := by
        rw [wVal_prefix hpref_r' (inpVec_length x) hfl_r_lt]
        have hx := hspr.2.2.2.2.2.2.2 x
        simpa [hx.1] using hx.2
      set sl := (l.leaves.map (fun p => (pigeonEdges G p).countP (fun e => x e))).sum
      set sr := (r.leaves.map (fun p => (pigeonEdges G p).countP (fun e => x e))).sum
      by_cases hlt_l : sl < l.size
      · refine ⟨(flagVar ha rl.2.flag, true), by simp [rl], ?_⟩
        rw [eval_flagVar ha x hfl_l_ge (by omega), hvl]
        exact decide_eq_true hlt_l
      · by_cases hlt_r : sr < r.size
        · refine ⟨(flagVar ha rr.2.flag, true), by simp [rr, rl], ?_⟩
          rw [eval_flagVar ha x hfl_r_ge (by omega), hvr]
          exact decide_eq_true hlt_r
        · refine ⟨(flagVar ha (buildP G w0 gs0 (.node l r)).2.flag, false), by simp [buildP, BuiltP.flag], ?_⟩
          rw [eval_flagVar ha x hfl_n_ge (by omega), hvn]
          exact decide_eq_false (by omega)

private def holeLeafClauses {n : ℕ} {G : BipGraph (n + 1) n} {a : ℕ} (ha : 0 < a)
    (h : Fin n) (sf tf : List ℕ) : Finset (Clause (GEdge G ⊕ Fin a)) :=
  {({(flagVar ha (sf.getLastD 0), false)} : Clause (GEdge G ⊕ Fin a)),
   ({(flagVar ha (tf.getLastD 0), false)} : Clause (GEdge G ⊕ Fin a))} ∪
  (Finset.univ : Finset (Fin (holeEdges G h).length)).biUnion (fun k =>
    let e := (holeEdges G h)[k]
    {({(flagVar ha (sf.getD k.val 0), false), (flagVar ha (sf.getD (k.val + 1) 0), true),
       (Sum.inl e, true)} : Clause (GEdge G ⊕ Fin a)),
     ({(flagVar ha (tf.getD k.val 0), false), (flagVar ha (tf.getD (k.val + 1) 0), true),
       (flagVar ha (sf.getD (k.val + 1) 0), true)} : Clause (GEdge G ⊕ Fin a)),
     ({(flagVar ha (tf.getD k.val 0), false), (flagVar ha (tf.getD (k.val + 1) 0), true),
       (Sum.inl e, true)} : Clause (GEdge G ⊕ Fin a))})

private lemma holeLeafClauses_width {n : ℕ} {G : BipGraph (n + 1) n} {a : ℕ} (ha : 0 < a)
    (h : Fin n) (sf tf : List ℕ) :
    ∀ cl ∈ holeLeafClauses (G := G) ha h sf tf, cl.card ≤ 3 := by
  intro cl hcl
  simp only [holeLeafClauses, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_univ, true_and] at hcl
  rcases hcl with (rfl | rfl) | ⟨k, rfl | rfl | rfl⟩
  · simp
  · simp
  · exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))
  · exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))
  · exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))

private lemma holeLeafClauses_card_le {n b : ℕ} {G : BipGraph (n + 1) n} (hRd : RightDegLe G b)
    {a : ℕ} (ha : 0 < a) (h : Fin n) (sf tf : List ℕ) :
    (holeLeafClauses (G := G) ha h sf tf).card ≤ 3 * b + 2 := by
  unfold holeLeafClauses
  have h2 : ({({(flagVar ha (sf.getLastD 0), false)} : Clause (GEdge G ⊕ Fin a)),
      ({(flagVar ha (tf.getLastD 0), false)} : Clause (GEdge G ⊕ Fin a))} : Finset _).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have h3 : ((Finset.univ : Finset (Fin (holeEdges G h).length)).biUnion (fun k =>
      let e := (holeEdges G h)[k]
      {({(flagVar ha (sf.getD k.val 0), false), (flagVar ha (sf.getD (k.val + 1) 0), true),
         (Sum.inl e, true)} : Clause (GEdge G ⊕ Fin a)),
       ({(flagVar ha (tf.getD k.val 0), false), (flagVar ha (tf.getD (k.val + 1) 0), true),
         (flagVar ha (sf.getD (k.val + 1) 0), true)} : Clause (GEdge G ⊕ Fin a)),
       ({(flagVar ha (tf.getD k.val 0), false), (flagVar ha (tf.getD (k.val + 1) 0), true),
         (Sum.inl e, true)} : Clause (GEdge G ⊕ Fin a))})).card ≤ 3 * b := by
    calc _ ≤ ∑ _k : Fin (holeEdges G h).length, 3 := by
          refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun k _ => ?_)
          exact le_trans (Finset.card_insert_le _ _)
            (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))
      _ = 3 * (holeEdges G h).length := by simp [mul_comm]
      _ = 3 * (rightNbrs G h).card := by rw [holeEdges_length]
      _ ≤ 3 * b := Nat.mul_le_mul_left 3 (hRd h)
  exact le_trans (Finset.card_union_le _ _) (by omega)

private def hClauses {n : ℕ} {G : BipGraph (n + 1) n} {a : ℕ} (ha : 0 < a) :
    BuiltH n G → Finset (Clause (GEdge G ⊕ Fin a))
  | .leaf h _ sf tf => holeLeafClauses ha h sf tf
  | .node l r _ f _ =>
    hClauses ha l ∪ hClauses ha r ∪
      {({(flagVar ha f, false), (flagVar ha l.flag, true), (flagVar ha r.flag, true)} : Clause (GEdge G ⊕ Fin a))}

private def BuiltH.leafCount {n : ℕ} {G : BipGraph (n + 1) n} : BuiltH n G → ℕ
  | .leaf _ _ _ _ => 1
  | .node l r _ _ _ => l.leafCount + r.leafCount

private lemma buildH_leafCount {n w0 : ℕ} (G : BipGraph (n + 1) n)
    (t : BTree (Fin n)) (gs : List Gate) :
    (buildH G w0 gs t).2.leafCount = t.size := by
  induction t generalizing gs with
  | leaf _ => rfl
  | node l r ihl ihr =>
    unfold buildH
    simp only [BuiltH.leafCount, BTree.size, ihl, ihr]

private lemma hClauses_width {n : ℕ} {G : BipGraph (n + 1) n} {a : ℕ} (ha : 0 < a)
    (t : BuiltH n G) : ∀ cl ∈ hClauses ha t, cl.card ≤ 3 := by
  induction t with
  | leaf h bs sf tf => exact holeLeafClauses_width ha h sf tf
  | node l r bs f sz ihl ihr =>
    intro cl hcl
    simp only [hClauses, Finset.mem_union, Finset.mem_singleton] at hcl
    rcases hcl with (h | h) | rfl
    · exact ihl cl h
    · exact ihr cl h
    · exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))

private lemma hClauses_card_le {n b : ℕ} {G : BipGraph (n + 1) n} (hRd : RightDegLe G b)
    {a : ℕ} (ha : 0 < a) (t : BuiltH n G) :
    (hClauses ha t).card + 1 ≤ (3 * b + 3) * t.leafCount := by
  induction t with
  | leaf h bs sf tf =>
    simp only [hClauses, BuiltH.leafCount, mul_one]
    have := holeLeafClauses_card_le hRd ha h sf tf
    omega
  | node l r bs f sz ihl ihr =>
    simp only [hClauses, BuiltH.leafCount]
    have h1 := Finset.card_union_le (hClauses ha l ∪ hClauses ha r)
      {({(flagVar ha f, false), (flagVar ha l.flag, true), (flagVar ha r.flag, true)} : Clause (GEdge G ⊕ Fin a))}
    have h2 := Finset.card_union_le (hClauses ha l) (hClauses ha r)
    have h3 : ({({(flagVar ha f, false), (flagVar ha l.flag, true), (flagVar ha r.flag, true)} : Clause (GEdge G ⊕ Fin a))} :
        Finset (Clause (GEdge G ⊕ Fin a))).card = 1 := Finset.card_singleton _
    nlinarith

private lemma hClauses_sat {n b w0 : ℕ} {G : BipGraph (n + 1) n}
    (hRd : RightDegLe G b) (hw0 : b < 2 ^ w0) (hw0_pos : 1 ≤ w0)
    (bt : BTree (Fin n)) (gs0 gs : List Gate)
    (hv0 : CValid (2 + Fintype.card (GEdge G)) gs0)
    (hpref : (buildH G w0 gs0 bt).1 <+: gs)
    (ha : 0 < gs.length) (x : GEdge G → Bool) :
    Satisfies (Sum.elim x (fun i : Fin gs.length => wVal gs (inpVec x) (2 + Fintype.card (GEdge G) + i.val)))
      (↑(hClauses ha (buildH G w0 gs0 bt).2) : Set (Clause (GEdge G ⊕ Fin gs.length))) := by
  induction bt generalizing gs0 with
  | leaf h =>
    have hsp := buildH_spec G hRd hw0 hw0_pos (.leaf h) gs0 hv0
    have hwf := BuiltH.wf_prefix rfl hpref hsp.2.2.2.2.2.1
    set r1 := mkSumList (2 + Fintype.card (GEdge G)) w0 gs0 ((holeEdges G h).map edgeWire)
    set r2 := mkHoleFlags (2 + Fintype.card (GEdge G)) r1.1 ((holeEdges G h).map edgeWire)
    have hrec := hwf.2.2.2.2.2.2.2.2 x
    have hsf_len : r2.2.1.length = (holeEdges G h).length + 1 := hwf.2.1
    have htf_len : r2.2.2.length = (holeEdges G h).length + 1 := hwf.2.2.1
    have hsf_b := hwf.2.2.2.1
    have htf_b := hwf.2.2.2.2.1
    have hsf_last_mem : r2.2.1.getLastD 0 ∈ r2.2.1 :=
      getLastD_mem_of_ne_nil (fun h' => by rw [h'] at hsf_len; simp at hsf_len) 0
    have htf_last_mem : r2.2.2.getLastD 0 ∈ r2.2.2 :=
      getLastD_mem_of_ne_nil (fun h' => by rw [h'] at htf_len; simp at htf_len) 0
    intro cl hcl
    simp only [Finset.mem_coe, buildH, hClauses, holeLeafClauses, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_univ, true_and] at hcl
    rcases hcl with (rfl | rfl) | ⟨k, rfl | rfl | rfl⟩
    · refine ⟨(flagVar ha (r2.2.1.getLastD 0), false), by simp [r2, r1], ?_⟩
      rw [eval_flagVar ha x (hsf_b _ hsf_last_mem).1 (hsf_b _ hsf_last_mem).2]
      exact hrec.1
    · refine ⟨(flagVar ha (r2.2.2.getLastD 0), false), by simp [r2, r1], ?_⟩
      rw [eval_flagVar ha x (htf_b _ htf_last_mem).1 (htf_b _ htf_last_mem).2]
      exact hrec.2.1
    · have hk1 : k.val < r2.2.1.length := by omega
      have hk2 : k.val + 1 < r2.2.1.length := by omega
      have hm1 : r2.2.1.getD k.val 0 ∈ r2.2.1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]; exact List.getElem_mem hk1
      have hm2 : r2.2.1.getD (k.val + 1) 0 ∈ r2.2.1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2]; exact List.getElem_mem hk2
      have heq := (hrec.2.2 k.val k.isLt).1
      cases hval : wVal gs (inpVec x) (r2.2.1.getD k.val 0)
      · refine ⟨(flagVar ha (r2.2.1.getD k.val 0), false), by simp [r2, r1], ?_⟩
        rw [eval_flagVar ha x (hsf_b _ hm1).1 (hsf_b _ hm1).2, hval]
      · rw [hval] at heq
        have hor : wVal gs (inpVec x) (r2.2.1.getD (k.val + 1) 0) = true ∨ x (holeEdges G h)[k] = true := by
          simpa [Bool.or_eq_true] using heq.symm
        rcases hor with hs | he
        · refine ⟨(flagVar ha (r2.2.1.getD (k.val + 1) 0), true), by simp [r2, r1], ?_⟩
          rw [eval_flagVar ha x (hsf_b _ hm2).1 (hsf_b _ hm2).2, hs]
        · refine ⟨(Sum.inl (holeEdges G h)[k], true), by simp [r2, r1], ?_⟩
          simpa using he
    · have hk1 : k.val < r2.2.2.length := by omega
      have hk2 : k.val + 1 < r2.2.2.length := by omega
      have hks2 : k.val + 1 < r2.2.1.length := by omega
      have hm1 : r2.2.2.getD k.val 0 ∈ r2.2.2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]; exact List.getElem_mem hk1
      have hm2 : r2.2.2.getD (k.val + 1) 0 ∈ r2.2.2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2]; exact List.getElem_mem hk2
      have hms2 : r2.2.1.getD (k.val + 1) 0 ∈ r2.2.1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hks2]; exact List.getElem_mem hks2
      have heq := (hrec.2.2 k.val k.isLt).2
      cases hval : wVal gs (inpVec x) (r2.2.2.getD k.val 0)
      · refine ⟨(flagVar ha (r2.2.2.getD k.val 0), false), by simp [r2, r1], ?_⟩
        rw [eval_flagVar ha x (htf_b _ hm1).1 (htf_b _ hm1).2, hval]
      · rw [hval] at heq
        have hor : wVal gs (inpVec x) (r2.2.2.getD (k.val + 1) 0) = true ∨
            (wVal gs (inpVec x) (r2.2.1.getD (k.val + 1) 0) = true ∧ x (holeEdges G h)[k] = true) := by
          simpa [Bool.or_eq_true, Bool.and_eq_true] using heq.symm
        rcases hor with ht | ⟨hs, _⟩
        · refine ⟨(flagVar ha (r2.2.2.getD (k.val + 1) 0), true), by simp [r2, r1], ?_⟩
          rw [eval_flagVar ha x (htf_b _ hm2).1 (htf_b _ hm2).2, ht]
        · refine ⟨(flagVar ha (r2.2.1.getD (k.val + 1) 0), true), by simp [r2, r1], ?_⟩
          rw [eval_flagVar ha x (hsf_b _ hms2).1 (hsf_b _ hms2).2, hs]
    · have hk1 : k.val < r2.2.2.length := by omega
      have hk2 : k.val + 1 < r2.2.2.length := by omega
      have hm1 : r2.2.2.getD k.val 0 ∈ r2.2.2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]; exact List.getElem_mem hk1
      have hm2 : r2.2.2.getD (k.val + 1) 0 ∈ r2.2.2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2]; exact List.getElem_mem hk2
      have heq := (hrec.2.2 k.val k.isLt).2
      cases hval : wVal gs (inpVec x) (r2.2.2.getD k.val 0)
      · refine ⟨(flagVar ha (r2.2.2.getD k.val 0), false), by simp [r2, r1], ?_⟩
        rw [eval_flagVar ha x (htf_b _ hm1).1 (htf_b _ hm1).2, hval]
      · rw [hval] at heq
        have hor : wVal gs (inpVec x) (r2.2.2.getD (k.val + 1) 0) = true ∨
            (wVal gs (inpVec x) (r2.2.1.getD (k.val + 1) 0) = true ∧ x (holeEdges G h)[k] = true) := by
          simpa [Bool.or_eq_true, Bool.and_eq_true] using heq.symm
        rcases hor with ht | ⟨_, he⟩
        · refine ⟨(flagVar ha (r2.2.2.getD (k.val + 1) 0), true), by simp [r2, r1], ?_⟩
          rw [eval_flagVar ha x (htf_b _ hm2).1 (htf_b _ hm2).2, ht]
        · refine ⟨(Sum.inl (holeEdges G h)[k], true), by simp [r2, r1], ?_⟩
          simpa using he
  | node l r ihl ihr =>
    have hsp := buildH_spec G hRd hw0 hw0_pos (.node l r) gs0 hv0
    have hspl := buildH_spec G hRd hw0 hw0_pos l gs0 hv0
    set rl := buildH G w0 gs0 l
    have hspr := buildH_spec G hRd hw0 hw0_pos r rl.1 hspl.1
    set rr := buildH G w0 rl.1 r
    have hpref_r : rr.1 <+: (buildH G w0 gs0 (.node l r)).1 := by
      unfold buildH
      set k := max rl.2.bits.length rr.2.bits.length
      have hm : 2 ≤ 2 + Fintype.card (GEdge G) := by omega
      have hlb : ∀ w ∈ rl.2.bits, w < 2 + Fintype.card (GEdge G) + rr.1.length := fun w hw => by
        have h1 : w < 2 + Fintype.card (GEdge G) + rl.1.length := by
          cases hlt : rl.2 with
          | leaf _ _ _ _ => have := hspl.2.2.2.2.2.1; rw [hlt] at this; exact this.1 w (by simpa [hlt, BuiltH.bits] using hw)
          | node _ _ _ _ _ => have := hspl.2.2.2.2.2.1; rw [hlt] at this; exact this.2.2.1 w (by simpa [hlt, BuiltH.bits] using hw)
        have h2 := List.IsPrefix.length_le hspr.2.1; omega
      have hrb : ∀ w ∈ rr.2.bits, w < 2 + Fintype.card (GEdge G) + rr.1.length := fun w hw => by
        cases hrt : rr.2 with
        | leaf _ _ _ _ => have := hspr.2.2.2.2.2.1; rw [hrt] at this; exact this.1 w (by simpa [hrt, BuiltH.bits] using hw)
        | node _ _ _ _ _ => have := hspr.2.2.2.2.2.1; rw [hrt] at this; exact this.2.2.1 w (by simpa [hrt, BuiltH.bits] using hw)
      have hadd := mkAddBits_spec hm hspr.1 (le_max_left _ _) (le_max_right _ _) hlb hrb
      have hfl := mkGtConst_spec hm hadd.1 hadd.2.2.2.2.1 (K := rl.2.sz + rr.2.sz) (by
        rw [hadd.2.2.2.1, hspl.2.2.2.2.1, hspr.2.2.2.2.1]
        have h1 := l.size_le_pow_height
        have h2 := r.size_le_pow_height
        have hkl : max rl.2.bits.length rr.2.bits.length = w0 + max l.height r.height := by
          rw [hspl.2.2.2.1, hspr.2.2.2.1]; omega
        rw [hkl]
        have hm1 : 2 ^ l.height ≤ 2 ^ max l.height r.height := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
        have hm2 : 2 ^ r.height ≤ 2 ^ max l.height r.height := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
        have hw2 : 2 ≤ 2 ^ w0 := by simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hw0_pos
        have hpow : 2 ^ (w0 + max l.height r.height + 1) = 2 ^ w0 * (2 * 2 ^ max l.height r.height) := by
          rw [pow_succ', pow_add]; ring
        rw [hpow]; nlinarith [Nat.two_pow_pos (max l.height r.height)])
      exact hadd.2.1.trans hfl.2.1
    have hpref_l : rl.1 <+: gs := hspr.2.1.trans (hpref_r.trans hpref)
    have hpref_r' : rr.1 <+: gs := hpref_r.trans hpref
    intro cl hcl
    simp only [Finset.mem_coe, buildH, hClauses, Finset.mem_union, Finset.mem_singleton] at hcl
    rcases hcl with (h | h) | rfl
    · exact ihl gs0 hv0 hpref_l cl (by simpa using h)
    · exact ihr rl.1 hspl.1 hpref_r' cl (by simpa using h)
    · have hfn := BuiltH.flag_lt hsp.2.2.2.2.2.1
      have hfl := BuiltH.flag_lt hspl.2.2.2.2.2.1
      have hfr := BuiltH.flag_lt hspr.2.2.2.2.2.1
      have hlen_n := List.IsPrefix.length_le hpref
      have hlen_l := List.IsPrefix.length_le hpref_l
      have hlen_r := List.IsPrefix.length_le hpref_r'
      have hvn : wVal gs (inpVec x) (buildH G w0 gs0 (.node l r)).2.flag =
          decide (l.size + r.size <
                  (l.leaves.map (fun h => (holeEdges G h).countP (fun e => x e))).sum +
                  (r.leaves.map (fun h => (holeEdges G h).countP (fun e => x e))).sum) := by
        rw [wVal_prefix hpref (inpVec_length x) hfn.2]
        have hx := hsp.2.2.2.2.2.2.2 x
        simpa [BTree.leaves, List.map_append, List.sum_append, BTree.size, hx.1] using hx.2
      have hvl : wVal gs (inpVec x) rl.2.flag =
          decide (l.size < (l.leaves.map (fun h => (holeEdges G h).countP (fun e => x e))).sum) := by
        rw [wVal_prefix hpref_l (inpVec_length x) hfl.2]
        have hx := hspl.2.2.2.2.2.2.2 x
        simpa [hx.1] using hx.2
      have hvr : wVal gs (inpVec x) rr.2.flag =
          decide (r.size < (r.leaves.map (fun h => (holeEdges G h).countP (fun e => x e))).sum) := by
        rw [wVal_prefix hpref_r' (inpVec_length x) hfr.2]
        have hx := hspr.2.2.2.2.2.2.2 x
        simpa [hx.1] using hx.2
      set sl := (l.leaves.map (fun h => (holeEdges G h).countP (fun e => x e))).sum
      set sr := (r.leaves.map (fun h => (holeEdges G h).countP (fun e => x e))).sum
      by_cases hgt_l : l.size < sl
      · refine ⟨(flagVar ha rl.2.flag, true), by simp [rl], ?_⟩
        rw [eval_flagVar ha x hfl.1 (by omega), hvl]
        exact decide_eq_true hgt_l
      · by_cases hgt_r : r.size < sr
        · refine ⟨(flagVar ha rr.2.flag, true), by simp [rr, rl], ?_⟩
          rw [eval_flagVar ha x hfr.1 (by omega), hvr]
          exact decide_eq_true hgt_r
        · refine ⟨(flagVar ha (buildH G w0 gs0 (.node l r)).2.flag, false), by simp [buildH, BuiltH.flag], ?_⟩
          rw [eval_flagVar ha x hfn.1 (by omega), hvn]
          exact decide_eq_false (by omega)

private structure Deriv {W : Type} [DecidableEq W] (F : Set (Clause W)) (B : ℕ) where
  lines : List (Clause W)
  hD : IsDerivation F lines
  hW : ∀ cl ∈ lines, cl.card ≤ B

private def Deriv.empty {W : Type} [DecidableEq W] (F : Set (Clause W)) (B : ℕ) : Deriv F B :=
  ⟨[], .nil, fun _ h => by simp at h⟩

private def Deriv.pushAx {W : Type} [DecidableEq W] {F : Set (Clause W)} {B : ℕ}
    (d : Deriv F B) (C : Clause W) (hC : C ∈ F) (hw : C.card ≤ B) : Deriv F B :=
  ⟨C :: d.lines, .ax d.hD hC, fun cl hcl => by
    simp only [List.mem_cons] at hcl
    rcases hcl with rfl | hcl
    · exact hw
    · exact d.hW cl hcl⟩

private def Deriv.pushRes {W : Type} [DecidableEq W] {F : Set (Clause W)} {B : ℕ}
    (d : Deriv F B) (C D R : Clause W) (hC : C ∈ d.lines) (hD : D ∈ d.lines)
    (hR : IsResolvent C D R) (hw : R.card ≤ B) : Deriv F B :=
  ⟨R :: d.lines, .res d.hD hC hD hR, fun cl hcl => by
    simp only [List.mem_cons] at hcl
    rcases hcl with rfl | hcl
    · exact hw
    · exact d.hW cl hcl⟩

private lemma erase_union_pair {W : Type} [DecidableEq W] {x y : W} {sx sy : Bool}
    (hne : (x, sx) ≠ (y, sy)) :
    ({(x, sx), (y, sy)} : Clause W).erase (x, sx) = {(y, sy)} := by
  ext l; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, rfl | rfl⟩
    · exact absurd rfl h1
    · rfl
  · rintro rfl
    exact ⟨hne.symm, Or.inr rfl⟩

private lemma erase_union_triple {W : Type} [DecidableEq W] {a b c : Literal W}
    (hab : a ≠ b) (hac : a ≠ c) :
    ({a, b, c} : Clause W).erase a = {b, c} := by
  ext l; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, rfl | rfl | rfl⟩
    · exact absurd rfl h1
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨hab.symm, Or.inr (Or.inl rfl)⟩
    · exact ⟨hac.symm, Or.inr (Or.inr rfl)⟩

private lemma derive_pigeon_leaf {n b a B : ℕ} {G : BipGraph (n + 1) n}
    (ha : 0 < a) (F : Set (Clause (GEdge G ⊕ Fin a)))
    (p : Fin (n + 1)) (f : ℕ) (hB : b + 1 ≤ B) (hdeg : (G p).card ≤ b)
    (hne : (pigeonEdges G p) ≠ [])
    (hax_row : ((Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = p ∧ l.2 = true)).image
      (fun l => ((Sum.inl l.1 : GEdge G ⊕ Fin a), l.2))) ∈ F)
    (hax_def : ∀ e ∈ pigeonEdges G p,
      ({(flagVar ha f, false), (Sum.inl e, false)} : Clause (GEdge G ⊕ Fin a)) ∈ F)
    (d : Deriv F B) :
    ∃ d' : Deriv F B,
      (∀ cl ∈ d.lines, cl ∈ d'.lines) ∧
      ({(flagVar ha f, false)} : Clause (GEdge G ⊕ Fin a)) ∈ d'.lines ∧
      d'.lines.length ≤ d.lines.length + (2 * b + 1) := by
  set es := pigeonEdges G p
  have hnd : es.Nodup := pigeonEdges_nodup G p
  have hlen : es.length ≤ b := by rw [pigeonEdges_length]; exact hdeg
  have hrow_eq : ((Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = p ∧ l.2 = true)).image
      (fun l => ((Sum.inl l.1 : GEdge G ⊕ Fin a), l.2))) =
      (es.map (fun e => (Sum.inl e, true))).toFinset := by
    ext l
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, List.mem_map, es, mem_pigeonEdges]
    constructor
    · rintro ⟨⟨e, s⟩, ⟨hp, rfl⟩, rfl⟩
      exact ⟨e, hp, rfl⟩
    · rintro ⟨e, hp, rfl⟩
      exact ⟨(e, true), ⟨hp, rfl⟩, rfl⟩
  have hrow_card : ((es.map (fun e => ((Sum.inl e : GEdge G ⊕ Fin a), true))).toFinset).card ≤ B := by
    have : ((es.map (fun e => ((Sum.inl e : GEdge G ⊕ Fin a), true))).toFinset).card ≤ es.length := by
      simpa using List.toFinset_card_le (l := es.map (fun e => ((Sum.inl e : GEdge G ⊕ Fin a), true)))
    omega

  let d0 := d.pushAx ((es.map (fun e => (Sum.inl e, true))).toFinset) (hrow_eq ▸ hax_row) hrow_card

  match hes : es, hne, hnd, hlen with
  | e0 :: rest, _, hnd_cons, hlen_cons =>
    have h1_le_b : 1 ≤ b := by simp only [List.length_cons] at hlen_cons; omega
    have hnd_e0 : e0 ∉ rest := (List.nodup_cons.mp hnd_cons).1
    have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd_cons).2

    have he0_mem : e0 ∈ es := by simp [hes]
    let d1 := d0.pushAx {(flagVar ha f, false), (Sum.inl e0, false)} (hax_def e0 he0_mem)
      (le_trans (Finset.card_insert_le _ _) (by simp; omega))
    let C1 : Clause (GEdge G ⊕ Fin a) :=
      insert (flagVar ha f, false) ((rest.map (fun e => (Sum.inl e, true))).toFinset)
    have hres1 : IsResolvent ((es.map (fun e => (Sum.inl e, true))).toFinset)
        {(flagVar ha f, false), (Sum.inl e0, false)} C1 := by
      refine ⟨Sum.inl e0, by simp [hes], by simp, ?_⟩
      ext l
      simp only [C1, hes, Finset.mem_insert, Finset.mem_union, Finset.mem_erase,
        List.mem_toFinset, List.mem_map, List.mem_cons, Finset.mem_singleton]
      constructor
      · rintro (rfl | ⟨e, he, rfl⟩)
        · exact Or.inr ⟨by simp [flagVar_ne_inl], Or.inl rfl⟩
        · have hne' : e ≠ e0 := fun h => hnd_e0 (h ▸ he)
          exact Or.inl ⟨by simp [hne'], ⟨e, Or.inr he, rfl⟩⟩
      · rintro (⟨h1, ⟨e, rfl | he, rfl⟩⟩ | ⟨h1, rfl | rfl⟩)
        · exact absurd rfl h1
        · exact Or.inr ⟨e, he, rfl⟩
        · exact Or.inl rfl
        · exact absurd rfl h1
    have hC1_card : C1.card ≤ B := by
      have h1 := Finset.card_insert_le (flagVar ha f, false) ((rest.map (fun e => ((Sum.inl e : GEdge G ⊕ Fin a), true))).toFinset)
      have h2 : ((rest.map (fun e => ((Sum.inl e : GEdge G ⊕ Fin a), true))).toFinset).card ≤ rest.length := by
        simpa using List.toFinset_card_le (l := rest.map (fun e => ((Sum.inl e : GEdge G ⊕ Fin a), true)))
      simp only [List.length_cons] at hlen_cons
      dsimp only [C1]
      omega
    let d2 := d1.pushRes _ _ C1 (by simp [d1, d0, Deriv.pushAx]) (by simp [d1, Deriv.pushAx]) hres1 hC1_card

    have hpeel : ∀ (ls : List (GEdge G)) (hnd_l : ls.Nodup)
        (hsub : ∀ e ∈ ls, e ∈ es) (dcur : Deriv F B)
        (hcur_in : insert (flagVar ha f, false) ((ls.map (fun e => (Sum.inl e, true))).toFinset) ∈ dcur.lines)
        (hlen_l : ls.length + 1 ≤ B),
        ∃ dfin : Deriv F B,
          (∀ cl ∈ dcur.lines, cl ∈ dfin.lines) ∧
          ({(flagVar ha f, false)} : Clause (GEdge G ⊕ Fin a)) ∈ dfin.lines ∧
          dfin.lines.length ≤ dcur.lines.length + 2 * ls.length := by
      intro ls
      induction ls with
      | nil =>
        intro _ _ dcur hcur_in _
        exact ⟨dcur, fun _ h => h, by simpa using hcur_in, by simp⟩
      | cons e ls' ih =>
        intro hnd_l hsub dcur hcur_in hlen_l
        have he_notin : e ∉ ls' := (List.nodup_cons.mp hnd_l).1
        have hnd' : ls'.Nodup := (List.nodup_cons.mp hnd_l).2
        let da := dcur.pushAx {(flagVar ha f, false), (Sum.inl e, false)}
          (hax_def e (hsub e (by simp))) (le_trans (Finset.card_insert_le _ _) (by simp; omega))
        let Cnext : Clause (GEdge G ⊕ Fin a) :=
          insert (flagVar ha f, false) ((ls'.map (fun e' => (Sum.inl e', true))).toFinset)
        have hres : IsResolvent
            (insert (flagVar ha f, false) (((e :: ls').map (fun e' => (Sum.inl e', true))).toFinset))
            {(flagVar ha f, false), (Sum.inl e, false)} Cnext := by
          refine ⟨Sum.inl e, by simp, by simp, ?_⟩
          ext l
          simp only [Cnext, Finset.mem_insert, Finset.mem_union, Finset.mem_erase,
            List.mem_toFinset, List.mem_map, List.mem_cons, Finset.mem_singleton]
          constructor
          · rintro (rfl | ⟨e', he', rfl⟩)
            · exact Or.inr ⟨by simp [flagVar_ne_inl], Or.inl rfl⟩
            · have hne' : e' ≠ e := fun h => he_notin (h ▸ he')
              exact Or.inl ⟨by simp [hne'], Or.inr ⟨e', Or.inr he', rfl⟩⟩
          · rintro (⟨h1, rfl | ⟨e', rfl | he', rfl⟩⟩ | ⟨h1, rfl | rfl⟩)
            · exact Or.inl rfl
            · exact absurd rfl h1
            · exact Or.inr ⟨e', he', rfl⟩
            · exact Or.inl rfl
            · exact absurd rfl h1
        have hCn_card : Cnext.card ≤ B := by
          have h1 := Finset.card_insert_le (flagVar ha f, false) ((ls'.map (fun e' => ((Sum.inl e' : GEdge G ⊕ Fin a), true))).toFinset)
          have h2 : ((ls'.map (fun e' => ((Sum.inl e' : GEdge G ⊕ Fin a), true))).toFinset).card ≤ ls'.length := by
            simpa using List.toFinset_card_le (l := ls'.map (fun e' => ((Sum.inl e' : GEdge G ⊕ Fin a), true)))
          simp only [List.length_cons] at hlen_l
          dsimp only [Cnext]
          omega
        let db := da.pushRes _ _ Cnext (List.mem_cons_of_mem _ hcur_in) List.mem_cons_self hres hCn_card
        obtain ⟨dfin, hsub_f, hmem_f, hlen_f⟩ := ih hnd' (fun u hu => hsub u (by simp [hu])) db
          List.mem_cons_self (by simp only [List.length_cons] at hlen_l; omega)
        refine ⟨dfin, fun cl hcl => hsub_f cl (by simp [db, da, Deriv.pushRes, Deriv.pushAx, hcl]), hmem_f, ?_⟩
        simp only [List.length_cons]
        have hdb : db.lines.length = dcur.lines.length + 2 := by simp [db, da, Deriv.pushRes, Deriv.pushAx]
        omega
    obtain ⟨dfin, hsub_f, hmem_f, hlen_f⟩ := hpeel rest hnd_rest (fun e he => by simp [hes, he]) d2
      List.mem_cons_self (by simp only [List.length_cons] at hlen_cons; omega)
    refine ⟨dfin, fun cl hcl => hsub_f cl (by simp [d2, d1, d0, Deriv.pushRes, Deriv.pushAx, hcl]),
      hmem_f, ?_⟩
    have hd2 : d2.lines.length = d.lines.length + 3 := by simp [d2, d1, d0, Deriv.pushRes, Deriv.pushAx]
    simp only [List.length_cons] at hlen_cons
    omega

private lemma card_triple_le {W : Type} [DecidableEq W] (a b c : W) {B : ℕ} (hB : 3 ≤ B) :
    ({a, b, c} : Finset W).card ≤ B := by
  have h1 := Finset.card_insert_le a ({b, c} : Finset W)
  have h2 := Finset.card_insert_le b ({c} : Finset W)
  simp at h2; omega

private lemma res_3_1 {W : Type} [DecidableEq W] {a b : Literal W} {v : W}
    (ha : a.1 ≠ v) (hb : b.1 ≠ v) :
    IsResolvent ({a, (v, true), b} : Clause W) {(v, false)} {a, b} := by
  refine ⟨v, by simp, by simp, ?_⟩
  ext l; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ⟨fun h => ha (congrArg Prod.fst h), Or.inl rfl⟩
    · exact Or.inl ⟨fun h => hb (congrArg Prod.fst h), Or.inr (Or.inr rfl)⟩
  · rintro (⟨hn, rfl | rfl | rfl⟩ | ⟨hn, rfl⟩)
    · exact Or.inl rfl
    · exact absurd rfl hn
    · exact Or.inr rfl
    · exact absurd rfl hn

private lemma res_2_1 {W : Type} [DecidableEq W] {a : Literal W} {v : W}
    (ha : a.1 ≠ v) :
    IsResolvent ({a, (v, true)} : Clause W) {(v, false)} {a} := by
  refine ⟨v, by simp, by simp, ?_⟩
  ext l; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro rfl; exact Or.inl ⟨fun h => ha (congrArg Prod.fst h), Or.inl rfl⟩
  · rintro (⟨hn, rfl | rfl⟩ | ⟨hn, rfl⟩)
    · rfl
    · exact absurd rfl hn
    · exact absurd rfl hn

private lemma res_2_2 {W : Type} [DecidableEq W] {a b : Literal W} {v : W}
    (ha : a.1 ≠ v) (hb : b.1 ≠ v) :
    IsResolvent ({a, (v, true)} : Clause W) {(v, false), b} {a, b} := by
  refine ⟨v, by simp, by simp, ?_⟩
  ext l; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ⟨fun h => ha (congrArg Prod.fst h), Or.inl rfl⟩
    · exact Or.inr ⟨fun h => hb (congrArg Prod.fst h), Or.inr rfl⟩
  · rintro (⟨hn, rfl | rfl⟩ | ⟨hn, rfl | rfl⟩)
    · exact Or.inl rfl
    · exact absurd rfl hn
    · exact absurd rfl hn
    · exact Or.inr rfl

private lemma res_3_2_to_3 {W : Type} [DecidableEq W] {a b c : Literal W} {v : W}
    (ha : a.1 ≠ v) (hb : b.1 ≠ v) (hc : c.1 ≠ v) :
    IsResolvent ({a, (v, true), b} : Clause W) {(v, false), c} {a, b, c} := by
  refine ⟨v, by simp, by simp, ?_⟩
  ext l; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨fun h => ha (congrArg Prod.fst h), Or.inl rfl⟩
    · exact Or.inl ⟨fun h => hb (congrArg Prod.fst h), Or.inr (Or.inr rfl)⟩
    · exact Or.inr ⟨fun h => hc (congrArg Prod.fst h), Or.inr rfl⟩
  · rintro (⟨hn, rfl | rfl | rfl⟩ | ⟨hn, rfl | rfl⟩)
    · exact Or.inl rfl
    · exact absurd rfl hn
    · exact Or.inr (Or.inl rfl)
    · exact absurd rfl hn
    · exact Or.inr (Or.inr rfl)

private lemma res_3_2_to_2 {W : Type} [DecidableEq W] {a b : Literal W} {v : W}
    (ha : a.1 ≠ v) (hb : b.1 ≠ v) :
    IsResolvent ({a, (v, true), b} : Clause W) {(v, false), b} {a, b} := by
  refine ⟨v, by simp, by simp, ?_⟩
  ext l; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ⟨fun h => ha (congrArg Prod.fst h), Or.inl rfl⟩
    · exact Or.inr ⟨fun h => hb (congrArg Prod.fst h), Or.inr rfl⟩
  · rintro (⟨hn, rfl | rfl | rfl⟩ | ⟨hn, rfl | rfl⟩)
    · exact Or.inl rfl
    · exact absurd rfl hn
    · exact Or.inr rfl
    · exact absurd rfl hn
    · exact Or.inr rfl

private lemma res_2_2_dup {W : Type} [DecidableEq W] {a : Literal W} {v : W}
    (ha : a.1 ≠ v) :
    IsResolvent ({a, (v, true)} : Clause W) {a, (v, false)} {a} := by
  refine ⟨v, by simp, by simp, ?_⟩
  ext l; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro rfl; exact Or.inl ⟨fun h => ha (congrArg Prod.fst h), Or.inl rfl⟩
  · rintro (⟨hn, rfl | rfl⟩ | ⟨hn, rfl | rfl⟩)
    · rfl
    · exact absurd rfl hn
    · rfl
    · exact absurd rfl hn

private lemma derive_hole_leaf {n b a B : ℕ} {G : BipGraph (n + 1) n}
    (ha : 0 < a) (F : Set (Clause (GEdge G ⊕ Fin a)))
    (h : Fin n) (sf tf : List ℕ) (hB : 3 ≤ B) (hdeg : (rightNbrs G h).card ≤ b)
    (hsf_len : sf.length = (holeEdges G h).length + 1)
    (htf_len : tf.length = (holeEdges G h).length + 1)
    (hsf_b : ∀ u ∈ sf, 2 + Fintype.card (GEdge G) ≤ u ∧ u < 2 + Fintype.card (GEdge G) + a)
    (htf_b : ∀ u ∈ tf, 2 + Fintype.card (GEdge G) ≤ u ∧ u < 2 + Fintype.card (GEdge G) + a)
    (hsf_nd : sf.Nodup) (htf_nd : tf.Nodup) (hdisj : ∀ u ∈ sf, u ∉ tf)
    (hax_pair : ∀ (e1 e2 : GEdge G), e1.1.2 = h → e2.1.2 = h → e1 ≠ e2 →
      ({(Sum.inl e1, false), (Sum.inl e2, false)} : Clause (GEdge G ⊕ Fin a)) ∈ F)
    (hax_leaf : ∀ cl ∈ holeLeafClauses ha h sf tf, cl ∈ F)
    (d : Deriv F B) :
    ∃ d' : Deriv F B,
      (∀ cl ∈ d.lines, cl ∈ d'.lines) ∧
      ({(flagVar ha (tf.headD 0), false)} : Clause (GEdge G ⊕ Fin a)) ∈ d'.lines ∧
      d'.lines.length ≤ d.lines.length + (4 * b * b + 12 * b + 2) := by
  set es := holeEdges G h
  set r := es.length
  have hr_le : r ≤ b := by simp only [r, es, holeEdges_length]; exact hdeg
  have hnd_es : es.Nodup := holeEdges_nodup G h
  have hgetLastD_eq : ∀ (l : List ℕ), 0 < l.length → l.getLastD 0 = l.getD (l.length - 1) 0 := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons x xs ih =>
      intro _
      cases xs with
      | nil => simp [List.getLastD]
      | cons y ys =>
        have h1 : (x :: y :: ys).getLastD 0 = (y :: ys).getLastD 0 := rfl
        rw [h1, ih (by simp)]
        simp
  have hsf_last_eq : sf.getLastD 0 = sf.getD r 0 := by
    rw [hgetLastD_eq sf (by omega)]
    congr 1; omega
  have htf_last_eq : tf.getLastD 0 = tf.getD r 0 := by
    rw [hgetLastD_eq tf (by omega)]
    congr 1; omega
  have hsf_mem : ∀ j ≤ r, sf.getD j 0 ∈ sf := fun j hj => by
    have hlt : j < sf.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
  have htf_mem : ∀ j ≤ r, tf.getD j 0 ∈ tf := fun j hj => by
    have hlt : j < tf.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
  have hsf_ne : ∀ j1 j2, j1 ≤ r → j2 ≤ r → j1 ≠ j2 →
      flagVar (V := GEdge G) ha (sf.getD j1 0) ≠ flagVar (V := GEdge G) ha (sf.getD j2 0) := by
    intro j1 j2 h1 h2 hne
    have h1' : j1 < sf.length := by omega
    have h2' : j2 < sf.length := by omega
    have hw_ne : sf.getD j1 0 ≠ sf.getD j2 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem h1', List.getElem?_eq_getElem h2']
      simp only [Option.getD_some]
      intro heq
      exact hne ((List.Nodup.getElem_inj_iff hsf_nd).mp heq)
    exact flagVar_inj ha (hsf_b _ (hsf_mem j1 h1)).1 (hsf_b _ (hsf_mem j1 h1)).2
      (hsf_b _ (hsf_mem j2 h2)).1 (hsf_b _ (hsf_mem j2 h2)).2 hw_ne
  have htf_ne : ∀ j1 j2, j1 ≤ r → j2 ≤ r → j1 ≠ j2 →
      flagVar (V := GEdge G) ha (tf.getD j1 0) ≠ flagVar (V := GEdge G) ha (tf.getD j2 0) := by
    intro j1 j2 h1 h2 hne
    have h1' : j1 < tf.length := by omega
    have h2' : j2 < tf.length := by omega
    have hw_ne : tf.getD j1 0 ≠ tf.getD j2 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem h1', List.getElem?_eq_getElem h2']
      simp only [Option.getD_some]
      intro heq
      exact hne ((List.Nodup.getElem_inj_iff htf_nd).mp heq)
    exact flagVar_inj ha (htf_b _ (htf_mem j1 h1)).1 (htf_b _ (htf_mem j1 h1)).2
      (htf_b _ (htf_mem j2 h2)).1 (htf_b _ (htf_mem j2 h2)).2 hw_ne
  have hst_ne : ∀ j1 j2, j1 ≤ r → j2 ≤ r →
      flagVar (V := GEdge G) ha (sf.getD j1 0) ≠ flagVar (V := GEdge G) ha (tf.getD j2 0) := by
    intro j1 j2 h1 h2
    have hw_ne : sf.getD j1 0 ≠ tf.getD j2 0 := fun heq =>
      hdisj _ (hsf_mem j1 h1) (heq ▸ htf_mem j2 h2)
    exact flagVar_inj ha (hsf_b _ (hsf_mem j1 h1)).1 (hsf_b _ (hsf_mem j1 h1)).2
      (htf_b _ (htf_mem j2 h2)).1 (htf_b _ (htf_mem j2 h2)).2 hw_ne

  have hs_last_ax : ({(flagVar ha (sf.getD r 0), false)} : Clause (GEdge G ⊕ Fin a)) ∈ F := by
    rw [← hsf_last_eq]; apply hax_leaf; simp [holeLeafClauses]
  have ht_last_ax : ({(flagVar ha (tf.getD r 0), false)} : Clause (GEdge G ⊕ Fin a)) ∈ F := by
    rw [← htf_last_eq]; apply hax_leaf; simp [holeLeafClauses]
  let d0 := (d.pushAx {(flagVar ha (sf.getD r 0), false)} hs_last_ax (by simp; omega)).pushAx
    {(flagVar ha (tf.getD r 0), false)} ht_last_ax (by simp; omega)

  have hderive_sk : ∀ (k : Fin r) (m : ℕ) (hm : m ≤ r - (k.val + 1)) (dcur : Deriv F B)
      (hsr : ({(flagVar ha (sf.getD r 0), false)} : Clause (GEdge G ⊕ Fin a)) ∈ dcur.lines),
      ∃ dfin : Deriv F B,
        (∀ cl ∈ dcur.lines, cl ∈ dfin.lines) ∧
        (if m = 0 then ({(flagVar ha (sf.getD r 0), false)} : Clause (GEdge G ⊕ Fin a)) ∈ dfin.lines
         else ({(flagVar ha (sf.getD (r - m) 0), false), (Sum.inl es[k], false)} : Clause (GEdge G ⊕ Fin a)) ∈ dfin.lines) ∧
        dfin.lines.length ≤ dcur.lines.length + 4 * m := by
    intro k m
    induction m with
    | zero =>
      intro _ dcur hsr
      exact ⟨dcur, fun _ h => h, by simpa using hsr, by simp⟩
    | succ m ih =>
      intro hm dcur hsr
      obtain ⟨d1, hsub1, hmem1, hlen1⟩ := ih (by omega) dcur hsr
      set j := r - (m + 1)
      have hj_lt : j < r := by omega
      have hj_gt : k.val < j := by omega
      have hj1 : j + 1 = r - m := by omega
      set ej := es[j]'hj_lt
      have hej_ne : ej ≠ es[k] := by
        intro heq
        have := (List.Nodup.getElem_inj_iff hnd_es).mp heq
        omega
      have hpair_in : ({(Sum.inl ej, false), (Sum.inl es[k], false)} : Clause (GEdge G ⊕ Fin a)) ∈ F :=
        hax_pair ej es[k] ((mem_holeEdges G h ej).mp (List.getElem_mem hj_lt))
          ((mem_holeEdges G h es[k]).mp (List.getElem_mem k.isLt)) hej_ne
      have hs_step_in : ({(flagVar ha (sf.getD j 0), false), (flagVar ha (sf.getD (j + 1) 0), true),
          (Sum.inl ej, true)} : Clause (GEdge G ⊕ Fin a)) ∈ F := by
        apply hax_leaf
        simp only [holeLeafClauses, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact Or.inr ⟨⟨j, hj_lt⟩, by simp [ej, es]⟩
      let da := d1.pushAx _ hs_step_in (card_triple_le _ _ _ hB)
      let db := da.pushAx _ hpair_in (le_trans (Finset.card_insert_le _ _) (by simp; omega))
      by_cases hm0 : m = 0
      · subst hm0
        simp only [↓reduceIte] at hmem1
        have hj1_r : j + 1 = r := by omega
        have hda_in : ({(flagVar ha (sf.getD j 0), false), (flagVar ha (sf.getD r 0), true),
            (Sum.inl ej, true)} : Clause (GEdge G ⊕ Fin a)) ∈ db.lines := by
          rw [← hj1_r]; exact List.mem_cons_of_mem _ List.mem_cons_self
        have hres1 := res_3_1
          (a := (flagVar (V := GEdge G) ha (sf.getD j 0), false))
          (b := (Sum.inl ej, true))
          (v := flagVar (V := GEdge G) ha (sf.getD r 0))
          (hsf_ne j r (by omega) le_rfl (by omega))
          (flagVar_ne_inl ha _ _).symm
        let dc := db.pushRes _ _ _ hda_in (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem1)) hres1
          (le_trans (Finset.card_insert_le _ _) (by simp; omega))
        have hres2 := res_2_2
          (a := (flagVar (V := GEdge G) ha (sf.getD j 0), false))
          (b := (Sum.inl es[k], false))
          (v := Sum.inl ej)
          (flagVar_ne_inl ha _ _)
          (fun h => hej_ne.symm (Sum.inl.inj h))
        let dd := dc.pushRes _ _ _ List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) hres2
          (le_trans (Finset.card_insert_le _ _) (by simp; omega))
        refine ⟨dd, fun cl hcl => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub1 cl hcl)))),
          by simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; exact List.mem_cons_self, ?_⟩
        have : dd.lines.length = d1.lines.length + 4 := rfl
        omega
      · simp only [hm0, ↓reduceIte] at hmem1
        rw [← hj1] at hmem1
        have hres1 := res_3_2_to_3
          (a := (flagVar (V := GEdge G) ha (sf.getD j 0), false))
          (b := (Sum.inl ej, true))
          (c := (Sum.inl es[k], false))
          (v := flagVar (V := GEdge G) ha (sf.getD (j + 1) 0))
          (hsf_ne j (j + 1) (by omega) (by omega) (by omega))
          (flagVar_ne_inl ha _ _).symm
          (flagVar_ne_inl ha _ _).symm
        let dc := db.pushRes _ _ _ (List.mem_cons_of_mem _ List.mem_cons_self)
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem1)) hres1
          (card_triple_le _ _ _ hB)
        have hres2 := res_3_2_to_2
          (a := (flagVar (V := GEdge G) ha (sf.getD j 0), false))
          (b := (Sum.inl es[k], false))
          (v := Sum.inl ej)
          (flagVar_ne_inl ha _ _)
          (fun h => hej_ne.symm (Sum.inl.inj h))
        let dd := dc.pushRes _ _ _ List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) hres2
          (le_trans (Finset.card_insert_le _ _) (by simp; omega))
        refine ⟨dd, fun cl hcl => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub1 cl hcl)))),
          by simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; exact List.mem_cons_self, ?_⟩
        have : dd.lines.length = d1.lines.length + 4 := rfl
        omega

  have hderive_t : ∀ (m : ℕ) (hm : m ≤ r) (dcur : Deriv F B)
      (hsr : ({(flagVar ha (sf.getD r 0), false)} : Clause (GEdge G ⊕ Fin a)) ∈ dcur.lines)
      (htr : ({(flagVar ha (tf.getD r 0), false)} : Clause (GEdge G ⊕ Fin a)) ∈ dcur.lines),
      ∃ dfin : Deriv F B,
        (∀ cl ∈ dcur.lines, cl ∈ dfin.lines) ∧
        ({(flagVar ha (tf.getD (r - m) 0), false)} : Clause (GEdge G ⊕ Fin a)) ∈ dfin.lines ∧
        dfin.lines.length ≤ dcur.lines.length + m * (4 * r + 6) := by
    intro m
    induction m with
    | zero =>
      intro _ dcur _ htr
      exact ⟨dcur, fun _ h => h, by simpa using htr, by simp⟩
    | succ m ih =>
      intro hm dcur hsr htr
      obtain ⟨d1, hsub1, htk1, hlen1⟩ := ih (by omega) dcur hsr htr
      set k := r - (m + 1)
      have hk_lt : k < r := by omega
      have hk1 : k + 1 = r - m := by omega
      rw [← hk1] at htk1

      obtain ⟨d2, hsub2, hsk, hlen2⟩ := hderive_sk ⟨k, hk_lt⟩ m (by dsimp only; omega) d1 (hsub1 _ hsr)
      have htk1' : ({(flagVar ha (tf.getD (k + 1) 0), false)} : Clause (GEdge G ⊕ Fin a)) ∈ d2.lines :=
        hsub2 _ htk1
      have hax_ts : ({(flagVar ha (tf.getD k 0), false), (flagVar ha (tf.getD (k + 1) 0), true),
          (flagVar ha (sf.getD (k + 1) 0), true)} : Clause (GEdge G ⊕ Fin a)) ∈ F := by
        apply hax_leaf
        simp only [holeLeafClauses, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact Or.inr ⟨⟨k, hk_lt⟩, by simp⟩
      have hax_te : ({(flagVar ha (tf.getD k 0), false), (flagVar ha (tf.getD (k + 1) 0), true),
          (Sum.inl (es[k]'hk_lt), true)} : Clause (GEdge G ⊕ Fin a)) ∈ F := by
        apply hax_leaf
        simp only [holeLeafClauses, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact Or.inr ⟨⟨k, hk_lt⟩, by simp [es]⟩
      by_cases hm0 : m = 0
      · subst hm0
        simp only [↓reduceIte] at hsk
        have hk1_r : k + 1 = r := by omega
        rw [hk1_r] at hax_ts htk1'
        let da := d2.pushAx _ hax_ts (card_triple_le _ _ _ hB)
        have hres1 := res_3_1
          (a := (flagVar (V := GEdge G) ha (tf.getD k 0), false))
          (b := (flagVar (V := GEdge G) ha (sf.getD r 0), true))
          (v := flagVar (V := GEdge G) ha (tf.getD r 0))
          (htf_ne k r (by omega) le_rfl (by omega))
          (hst_ne r r le_rfl le_rfl)
        let db := da.pushRes _ _ _ List.mem_cons_self (List.mem_cons_of_mem _ htk1') hres1
          (le_trans (Finset.card_insert_le _ _) (by simp; omega))
        have hres2 := res_2_1
          (a := (flagVar (V := GEdge G) ha (tf.getD k 0), false))
          (v := flagVar (V := GEdge G) ha (sf.getD r 0))
          (hst_ne r k le_rfl (by omega)).symm
        let dc := db.pushRes _ _ _ List.mem_cons_self (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hsk)) hres2
          (by simp; omega)
        refine ⟨dc, fun cl hcl => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub2 cl (hsub1 cl hcl)))),
          List.mem_cons_self, ?_⟩
        have : dc.lines.length = d2.lines.length + 3 := rfl
        simp only [Nat.zero_add, one_mul, mul_zero, add_zero] at hlen1 hlen2 ⊢
        omega
      · simp only [hm0, ↓reduceIte] at hsk
        rw [← hk1] at hsk
        let da := d2.pushAx _ hax_ts (card_triple_le _ _ _ hB)
        let db := da.pushAx _ hax_te (card_triple_le _ _ _ hB)
        have hres1 := res_3_1
          (a := (flagVar (V := GEdge G) ha (tf.getD k 0), false))
          (b := (flagVar (V := GEdge G) ha (sf.getD (k + 1) 0), true))
          (v := flagVar (V := GEdge G) ha (tf.getD (k + 1) 0))
          (htf_ne k (k + 1) (by omega) (by omega) (by omega))
          (hst_ne (k + 1) (k + 1) (by omega) (by omega))
        let dc := db.pushRes _ _ _ (List.mem_cons_of_mem _ List.mem_cons_self)
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htk1')) hres1
          (le_trans (Finset.card_insert_le _ _) (by simp; omega))
        have hres2 := res_2_2
          (a := (flagVar (V := GEdge G) ha (tf.getD k 0), false))
          (b := (Sum.inl (es[k]'hk_lt), false))
          (v := flagVar (V := GEdge G) ha (sf.getD (k + 1) 0))
          (hst_ne (k + 1) k (by omega) (by omega)).symm
          (flagVar_ne_inl ha _ _).symm
        let dd := dc.pushRes _ _ _ List.mem_cons_self
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hsk))) hres2
          (le_trans (Finset.card_insert_le _ _) (by simp; omega))
        have hres3 := res_3_1
          (a := (flagVar (V := GEdge G) ha (tf.getD k 0), false))
          (b := (Sum.inl (es[k]'hk_lt), true))
          (v := flagVar (V := GEdge G) ha (tf.getD (k + 1) 0))
          (htf_ne k (k + 1) (by omega) (by omega) (by omega))
          (flagVar_ne_inl ha _ _).symm
        let de := dd.pushRes _ _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ htk1')))) hres3
          (le_trans (Finset.card_insert_le _ _) (by simp; omega))
        have hres4 := res_2_2_dup
          (a := (flagVar (V := GEdge G) ha (tf.getD k 0), false))
          (v := Sum.inl (es[k]'hk_lt))
          (flagVar_ne_inl ha _ _)
        let df := de.pushRes _ _ _ List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) hres4
          (by simp; omega)
        refine ⟨df, fun cl hcl => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsub2 cl (hsub1 cl hcl))))))),
          List.mem_cons_self, ?_⟩
        have : df.lines.length = d2.lines.length + 6 := rfl
        rw [Nat.succ_mul]
        omega
  obtain ⟨dfin, hsub, hmem, hlen⟩ := hderive_t r le_rfl d0
    (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self
  have hhd : tf.headD 0 = tf.getD (r - r) 0 := by
    simp only [Nat.sub_self]; cases tf <;> rfl
  refine ⟨dfin, fun cl hcl => hsub cl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hcl)), by rwa [hhd], ?_⟩
  have hd0 : d0.lines.length = d.lines.length + 2 := rfl
  have hr2 : r * (4 * r + 6) ≤ b * (4 * b + 6) :=
    Nat.mul_le_mul hr_le (by omega)
  have hbb : b * (4 * b + 6) = 4 * b * b + 6 * b := by ring
  omega

private lemma derive_node_step {W : Type} [DecidableEq W] {F : Set (Clause W)} {B : ℕ}
    (hB : 3 ≤ B) (v l r : W) (hvl : v ≠ l) (hvr : v ≠ r) (hlr : l ≠ r)
    (hax : ({(v, false), (l, true), (r, true)} : Clause W) ∈ F)
    (d : Deriv F B)
    (hl : ({(l, false)} : Clause W) ∈ d.lines) (hr : ({(r, false)} : Clause W) ∈ d.lines) :
    ∃ d' : Deriv F B,
      (∀ cl ∈ d.lines, cl ∈ d'.lines) ∧
      ({(v, false)} : Clause W) ∈ d'.lines ∧
      d'.lines.length = d.lines.length + 3 := by
  let d1 := d.pushAx {(v, false), (l, true), (r, true)} hax
    (by
      have h1 := Finset.card_insert_le (v, false) {(l, true), (r, true)}
      have h2 := Finset.card_insert_le (l, true) {(r, true)}
      simp at h2; omega)
  have hres1 : IsResolvent {(v, false), (l, true), (r, true)} {(l, false)} {(v, false), (r, true)} := by
    refine ⟨l, by simp, by simp, ?_⟩
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl ⟨by simp [hvl], Or.inl rfl⟩
      · exact Or.inl ⟨by simp [hlr.symm], Or.inr (Or.inr rfl)⟩
    · rintro (⟨hn, rfl | rfl | rfl⟩ | ⟨hn, rfl⟩)
      · exact Or.inl rfl
      · exact absurd rfl hn
      · exact Or.inr rfl
      · exact absurd rfl hn
  let d2 := d1.pushRes _ _ {(v, false), (r, true)}
    (by simp [d1, Deriv.pushAx]) (by simp [d1, Deriv.pushAx, hl]) hres1
    (le_trans (Finset.card_insert_le _ _) (by simp; omega))
  have hres2 : IsResolvent {(v, false), (r, true)} {(r, false)} {(v, false)} := by
    refine ⟨r, by simp, by simp, ?_⟩
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro rfl; exact Or.inl ⟨by simp [hvr], Or.inl rfl⟩
    · rintro (⟨hn, rfl | rfl⟩ | ⟨hn, rfl⟩)
      · rfl
      · exact absurd rfl hn
      · exact absurd rfl hn
  let d3 := d2.pushRes _ _ {(v, false)}
    (by simp [d2, Deriv.pushRes]) (by simp [d2, d1, Deriv.pushRes, Deriv.pushAx, hr]) hres2
    (by simp; omega)
  exact ⟨d3, fun cl hcl => by simp [d3, d2, d1, Deriv.pushRes, Deriv.pushAx, hcl],
    by simp [d3, Deriv.pushRes], by simp [d3, d2, d1, Deriv.pushRes, Deriv.pushAx]⟩

private lemma derive_pTree {n b a B : ℕ} {G : BipGraph (n + 1) n}
    (ha : 0 < a) (F : Set (Clause (GEdge G ⊕ Fin a)))
    (hB : max (b + 1) 3 ≤ B) (hLd : LeftDegLe G b)
    (hne_p : ∀ p : Fin (n + 1), pigeonEdges G p ≠ [])
    (hax_row : ∀ p : Fin (n + 1),
      ((Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = p ∧ l.2 = true)).image
        (fun l => ((Sum.inl l.1 : GEdge G ⊕ Fin a), l.2))) ∈ F)
    (gs : List Gate) (hgs_len : gs.length = a)
    (t : BuiltP n G) (hwf : t.Wf (2 + Fintype.card (GEdge G)) gs)
    (hax_t : ∀ cl ∈ pClauses ha t, cl ∈ F)
    (d : Deriv F B) :
    ∃ d' : Deriv F B,
      (∀ cl ∈ d.lines, cl ∈ d'.lines) ∧
      ({(flagVar ha t.flag, false)} : Clause (GEdge G ⊕ Fin a)) ∈ d'.lines ∧
      d'.lines.length + 3 ≤ d.lines.length + (2 * b + 4) * t.leafCount := by
  induction t generalizing d with
  | leaf p bs f =>
    obtain ⟨d', hsub, hmem, hlen⟩ := derive_pigeon_leaf ha F p f (by omega) (hLd p) (hne_p p)
      (hax_row p) (fun e he => hax_t _ (by simp only [pClauses, List.mem_toFinset, List.mem_map]; exact ⟨e, he, rfl⟩)) d
    exact ⟨d', hsub, hmem, by simp only [BuiltP.leafCount, mul_one]; omega⟩
  | node l r bs f sz ihl ihr =>
    obtain ⟨d1, hsub1, hmem1, hlen1⟩ := ihl hwf.1
      (fun cl hcl => hax_t cl (by simp [pClauses, hcl])) d
    obtain ⟨d2, hsub2, hmem2, hlen2⟩ := ihr hwf.2.1
      (fun cl hcl => hax_t cl (by simp [pClauses, hcl])) d1
    have hl_b : 2 + Fintype.card (GEdge G) ≤ l.flag ∧ l.flag < 2 + Fintype.card (GEdge G) + a := by
      cases l with
      | leaf _ _ _ => exact ⟨hwf.1.2.1, by dsimp only [BuiltP.flag]; have := hwf.1.2.2; omega⟩
      | node _ _ _ _ _ => exact ⟨hwf.1.2.2.2.1, by dsimp only [BuiltP.flag]; have := hwf.1.2.2.2.2.1; omega⟩
    have hr_b : 2 + Fintype.card (GEdge G) ≤ r.flag ∧ r.flag < 2 + Fintype.card (GEdge G) + a := by
      cases r with
      | leaf _ _ _ => exact ⟨hwf.2.1.2.1, by dsimp only [BuiltP.flag]; have := hwf.2.1.2.2; omega⟩
      | node _ _ _ _ _ => exact ⟨hwf.2.1.2.2.2.1, by dsimp only [BuiltP.flag]; have := hwf.2.1.2.2.2.2.1; omega⟩
    have hf_b : 2 + Fintype.card (GEdge G) ≤ f ∧ f < 2 + Fintype.card (GEdge G) + a :=
      ⟨hwf.2.2.2.1, by have := hwf.2.2.2.2.1; omega⟩
    have hfl_ne : flagVar ha f ≠ flagVar ha l.flag :=
      flagVar_inj ha hf_b.1 hf_b.2 hl_b.1 hl_b.2 (by have := hwf.2.2.2.2.2.1; have := hwf.2.2.2.2.2.2; omega)
    have hfr_ne : flagVar ha f ≠ flagVar ha r.flag :=
      flagVar_inj ha hf_b.1 hf_b.2 hr_b.1 hr_b.2 (by have := hwf.2.2.2.2.2.2; omega)
    have hlr_ne : flagVar ha l.flag ≠ flagVar ha r.flag :=
      flagVar_inj ha hl_b.1 hl_b.2 hr_b.1 hr_b.2 (by have := hwf.2.2.2.2.2.1; omega)
    have hax_n : ({(flagVar ha f, false), (flagVar ha l.flag, true), (flagVar ha r.flag, true)} :
        Clause (GEdge G ⊕ Fin a)) ∈ F := hax_t _ (by simp [pClauses])
    obtain ⟨d3, hsub3, hmem3, hlen3⟩ := derive_node_step (by omega)
      (flagVar ha f) (flagVar ha l.flag) (flagVar ha r.flag) hfl_ne hfr_ne hlr_ne hax_n d2
      (hsub2 _ hmem1) hmem2
    refine ⟨d3, fun cl hcl => hsub3 cl (hsub2 cl (hsub1 cl hcl)), hmem3, ?_⟩
    simp only [BuiltP.leafCount, mul_add]
    omega

private lemma derive_hTree {n b a B : ℕ} {G : BipGraph (n + 1) n}
    (ha : 0 < a) (F : Set (Clause (GEdge G ⊕ Fin a)))
    (hB : 3 ≤ B) (hRd : RightDegLe G b)
    (hax_pair : ∀ (h : Fin n) (e1 e2 : GEdge G), e1.1.2 = h → e2.1.2 = h → e1 ≠ e2 →
      ({(Sum.inl e1, false), (Sum.inl e2, false)} : Clause (GEdge G ⊕ Fin a)) ∈ F)
    (gs : List Gate) (hgs_len : gs.length = a)
    (t : BuiltH n G) (hwf : t.Wf (2 + Fintype.card (GEdge G)) gs)
    (hax_t : ∀ cl ∈ hClauses ha t, cl ∈ F)
    (d : Deriv F B) :
    ∃ d' : Deriv F B,
      (∀ cl ∈ d.lines, cl ∈ d'.lines) ∧
      ({(flagVar ha t.flag, false)} : Clause (GEdge G ⊕ Fin a)) ∈ d'.lines ∧
      d'.lines.length + 3 ≤ d.lines.length + (4 * b * b + 12 * b + 5) * t.leafCount := by
  induction t generalizing d with
  | leaf h bs sf tf =>
    obtain ⟨d', hsub, hmem, hlen⟩ := derive_hole_leaf ha F h sf tf hB (hRd h)
      hwf.2.1 hwf.2.2.1
      (fun u hu => ⟨(hwf.2.2.2.1 u hu).1, by have := (hwf.2.2.2.1 u hu).2; omega⟩)
      (fun u hu => ⟨(hwf.2.2.2.2.1 u hu).1, by have := (hwf.2.2.2.2.1 u hu).2; omega⟩)
      hwf.2.2.2.2.2.1 hwf.2.2.2.2.2.2.1 hwf.2.2.2.2.2.2.2.1
      (hax_pair h) (fun cl hcl => hax_t cl (by simpa [hClauses] using hcl)) d
    exact ⟨d', hsub, hmem, by simp only [BuiltH.leafCount, mul_one]; omega⟩
  | node l r bs f sz ihl ihr =>
    obtain ⟨d1, hsub1, hmem1, hlen1⟩ := ihl hwf.1
      (fun cl hcl => hax_t cl (by simp [hClauses, hcl])) d
    obtain ⟨d2, hsub2, hmem2, hlen2⟩ := ihr hwf.2.1
      (fun cl hcl => hax_t cl (by simp [hClauses, hcl])) d1
    have hl_b := BuiltH.flag_lt hwf.1
    have hr_b := BuiltH.flag_lt hwf.2.1
    have hf_b : 2 + Fintype.card (GEdge G) ≤ f ∧ f < 2 + Fintype.card (GEdge G) + a :=
      ⟨hwf.2.2.2.1, by have := hwf.2.2.2.2.1; omega⟩
    have hfl_ne : flagVar ha f ≠ flagVar ha l.flag :=
      flagVar_inj ha hf_b.1 hf_b.2 hl_b.1 (by omega) (by have := hwf.2.2.2.2.2.1; have := hwf.2.2.2.2.2.2; omega)
    have hfr_ne : flagVar ha f ≠ flagVar ha r.flag :=
      flagVar_inj ha hf_b.1 hf_b.2 hr_b.1 (by omega) (by have := hwf.2.2.2.2.2.2; omega)
    have hlr_ne : flagVar ha l.flag ≠ flagVar ha r.flag :=
      flagVar_inj ha hl_b.1 (by omega) hr_b.1 (by omega) (by have := hwf.2.2.2.2.2.1; omega)
    have hax_n : ({(flagVar ha f, false), (flagVar ha l.flag, true), (flagVar ha r.flag, true)} :
        Clause (GEdge G ⊕ Fin a)) ∈ F := hax_t _ (by simp [hClauses])
    obtain ⟨d3, hsub3, hmem3, hlen3⟩ := derive_node_step hB
      (flagVar ha f) (flagVar ha l.flag) (flagVar ha r.flag) hfl_ne hfr_ne hlr_ne hax_n d2
      (hsub2 _ hmem1) hmem2
    refine ⟨d3, fun cl hcl => hsub3 cl (hsub2 cl (hsub1 cl hcl)), hmem3, ?_⟩
    simp only [BuiltH.leafCount, mul_add]
    omega

private lemma upper_bound_on_expander (b s₀ n : ℕ) (hs₀ : 0 < s₀) (hn_s : s₀ ≤ n) (hn_pos : 1 ≤ n)
    (G : BipGraph (n + 1) n) (hLd : LeftDegLe G b) (hRd : RightDegLe G b)
    (hE : IsBdryExpander G (n / s₀) 2) :
    let w0 := Nat.clog 2 (b + 1) + 1
    let C_up := max (max (b + 1) 3) (6 * ((5 * w0 * b + 3 * b + 15 * w0 + 16) * 3 + 13 * 12) +
      (4 * b * b + 20 * b + 20) * 3 + 20)
    let V := GEdge G
    let e := Fintype.card V
    let F := funGraphPHP G
    let lift := fun (a : ℕ) (cl : Clause V) =>
      cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin a), l.2))
    let allowed := fun (H : Circuit) =>
      ReadsBack (2 + e) H ∧
      ∀ g ∈ H.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
        g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)
    let value := fun (a : ℕ) (H : Circuit) (pick : Fin a → Fin (2 + e + H.size))
        (x : V → Bool) (i : Fin a) =>
      (H.wires ([false, true] ++ List.ofFn (fun j : Fin e => x ((Fintype.equivFin V).symm j)))).getD
        (pick i).val false
    ∃ (a : ℕ) (extra : Finset (Clause (V ⊕ Fin a)))
        (H : Circuit) (pick : Fin a → Fin (2 + e + H.size)),
      allowed H ∧ (∀ g ∈ H.gates, g.inputs.length ≤ 2) ∧
      a + H.size + extra.card ≤ C_up * n ∧ (∀ cl ∈ extra, cl.card ≤ 3) ∧
      (∀ (x : V → Bool) (y : Fin a → Bool),
        Satisfies (Sum.elim x y) (↑extra : Set (Clause (V ⊕ Fin a))) ↔ y = value a H pick x) ∧
      ∃ π : List (Clause (V ⊕ Fin a)),
        IsRefutation (Set.image (lift a) F ∪ (↑extra : Set (Clause (V ⊕ Fin a)))) π ∧
        π.length ≤ C_up * n ∧ ∀ cl ∈ π, cl.card ≤ C_up := by
  intro w0 C_up V e F lift allowed value
  have hw0_pos : 1 ≤ w0 := by omega
  have hw0_gt : b < 2 ^ w0 := by
    have h1 : b + 1 ≤ 2 ^ Nat.clog 2 (b + 1) := Nat.le_pow_clog (by omega) (b + 1)
    have h2 : 2 ^ Nat.clog 2 (b + 1) ≤ 2 ^ w0 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hp_ne : List.finRange (n + 1) ≠ [] := by
    intro h; have := congrArg List.length h; simp at this
  have hh_ne : List.finRange n ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  set btP := mkBalanced (List.finRange (n + 1)) hp_ne with hbtP
  set btH := mkBalanced (List.finRange n) hh_ne with hbtH
  set resP := buildP G w0 [] btP with hresP
  have hP := buildP_spec G hLd hw0_gt hw0_pos btP [] (cvalid_nil (2 + e))
  dsimp only at hP; rw [← hresP] at hP
  set resH := buildH G w0 resP.1 btH with hresH
  have hH := buildH_spec G hRd hw0_gt hw0_pos btH resP.1 hP.1
  dsimp only at hH; rw [← hresH] at hH
  set gs := resH.1
  set a := gs.length
  set H : Circuit := ⟨gs, 0⟩
  have hP_pos : 0 < resP.1.length := by
    have h1 : 2 + e + [].length ≤ resP.2.flag := hP.2.2.2.2.2.2.1
    have h2 : resP.2.flag < 2 + e + resP.1.length := by
      cases hp : resP.2 with
      | leaf _ _ _ => have := hP.2.2.2.2.2.1; rw [hp] at this; exact this.2.2
      | node _ _ _ _ _ => have := hP.2.2.2.2.2.1; rw [hp] at this; exact this.2.2.2.2.1
    simp only [List.length_nil, add_zero] at h1
    omega
  have ha : 0 < a := lt_of_lt_of_le hP_pos (List.IsPrefix.length_le hH.2.1)
  set pick : Fin a → Fin (2 + e + H.size) := fun i => ⟨2 + e + i.val, by simp [H, Circuit.size, a]⟩
  set topCl : Clause (V ⊕ Fin a) :=
    {(flagVar ha resP.2.flag, true), (flagVar ha resH.2.flag, true)}
  set extra : Finset (Clause (V ⊕ Fin a)) :=
    tseitinAll (V := V) gs ∪ pClauses ha resP.2 ∪ hClauses ha resH.2 ∪ {topCl}
  have hP_sz : btP.size = n + 1 := by rw [mkBalanced_size]; simp
  have hH_sz : btH.size = n := by rw [mkBalanced_size]; simp
  have hP_sh : btP.sumHeight ≤ 4 * (n + 1) := by
    have := mkBalanced_sumHeight (List.finRange (n + 1)) hp_ne
    rw [← hbtP] at this
    simp only [List.length_finRange] at this
    omega
  have hH_sh : btH.sumHeight ≤ 4 * n := by
    have := mkBalanced_sumHeight (List.finRange n) hh_ne
    rw [← hbtH] at this
    simp only [List.length_finRange] at this
    omega
  have hgs_bound : a ≤ ((5 * w0 * b + 3 * b + 15 * w0 + 16) * 3 + 13 * 12) * n := by
    have hp1 : resP.1.length ≤ (5 * w0 * b + 15 * w0 + 16) * (n + 1) + 13 * btP.sumHeight := by
      have := hP.2.2.1
      simp only [List.length_nil, zero_add] at this
      rw [hP_sz] at this; omega
    have hh1 : resH.1.length ≤ resP.1.length + (5 * w0 * b + 3 * b + 15 * w0 + 16) * n + 13 * btH.sumHeight := by
      have h := hH.2.2.1
      rw [hH_sz] at h
      exact le_trans (Nat.le_add_right _ _) h
    have hK : (5 * w0 * b + 15 * w0 + 16) * (n + 1) ≤ (5 * w0 * b + 3 * b + 15 * w0 + 16) * (2 * n) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hsh : 13 * btP.sumHeight + 13 * btH.sumHeight ≤ 13 * 12 * n := by omega
    have ha_eq : a = resH.1.length := rfl
    calc a ≤ (5 * w0 * b + 3 * b + 15 * w0 + 16) * (2 * n) +
             (5 * w0 * b + 3 * b + 15 * w0 + 16) * n + 13 * 12 * n := by omega
      _ = ((5 * w0 * b + 3 * b + 15 * w0 + 16) * 3 + 13 * 12) * n := by ring
  have hextra_card : extra.card ≤ 3 * a + (b + 1) * (n + 1) + (3 * b + 3) * n + 1 := by
    have ht := tseitinAll_card_le (V := V) gs
    have hp := pClauses_card_le hLd ha resP.2
    have hh := hClauses_card_le hRd ha resH.2
    rw [buildP_leafCount, hP_sz] at hp
    rw [buildH_leafCount, hH_sz] at hh
    have hu1 := Finset.card_union_le (tseitinAll (V := V) gs ∪ pClauses ha resP.2 ∪ hClauses ha resH.2) {topCl}
    have hu2 := Finset.card_union_le (tseitinAll (V := V) gs ∪ pClauses ha resP.2) (hClauses ha resH.2)
    have hu3 := Finset.card_union_le (tseitinAll (V := V) gs) (pClauses ha resP.2)
    have hts : ({topCl} : Finset (Clause (V ⊕ Fin a))).card = 1 := Finset.card_singleton _
    have hgs_a : gs.length = a := rfl
    dsimp only [extra]
    omega
  have hallow_H : allowed H := by
    refine ⟨hH.1.1, fun g hg => ?_⟩
    rcases hH.1.2 g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hlen_H : ∀ g ∈ H.gates, g.inputs.length ≤ 2 := fun g hg => simpleGate_len_le (hH.1.2 g hg)
  have hextra_width : ∀ cl ∈ extra, cl.card ≤ 3 := by
    intro cl hcl
    simp only [extra, Finset.mem_union, Finset.mem_singleton] at hcl
    rcases hcl with ((h | h) | h) | rfl
    · exact tseitinAll_width gs cl h
    · exact pClauses_width ha resP.2 cl h
    · exact hClauses_width ha resH.2 cl h
    · exact le_trans (Finset.card_insert_le _ _) (by simp)
  have hval_eq : ∀ x : V → Bool, value a H pick x = fun i : Fin a => wVal gs (inpVec x) (2 + e + i.val) := by
    intro x; funext i; rfl
  have hP_fl_b : 2 + e ≤ resP.2.flag ∧ resP.2.flag < 2 + e + resP.1.length := by
    cases hp : resP.2 with
    | leaf _ _ _ => have := hP.2.2.2.2.2.1; rw [hp] at this; exact ⟨this.2.1, this.2.2⟩
    | node _ _ _ _ _ => have := hP.2.2.2.2.2.1; rw [hp] at this; exact ⟨this.2.2.2.1, this.2.2.2.2.1⟩
  have hH_fl_b := BuiltH.flag_lt hH.2.2.2.2.2.1
  have htop_sat : ∀ x : V → Bool, ClauseSat (Sum.elim x (value a H pick x)) topCl := by
    intro x
    rw [hval_eq x]
    have hP_len_le := List.IsPrefix.length_le hH.2.1
    have hP_val : wVal gs (inpVec x) resP.2.flag =
        decide ((∑ p : Fin (n + 1), (pigeonEdges G p).countP (fun e => x e)) < n + 1) := by
      rw [wVal_prefix hH.2.1 (inpVec_length x) hP_fl_b.2]
      have hx := hP.2.2.2.2.2.2.2 x
      rw [hx.2, hx.1, hP_sz, mkBalanced_leaves]
      congr 1
    have hH_val : wVal gs (inpVec x) resH.2.flag =
        decide (n < (∑ h : Fin n, (holeEdges G h).countP (fun e => x e))) := by
      have hx := hH.2.2.2.2.2.2.2 x
      rw [hx.2, hx.1, hH_sz, mkBalanced_leaves]
      congr 1
    have hsum_eq := sum_pigeon_eq_sum_hole G x
    set S := ∑ p : Fin (n + 1), (pigeonEdges G p).countP (fun e => x e)
    by_cases hlt : S < n + 1
    · refine ⟨(flagVar ha resP.2.flag, true), by simp [topCl], ?_⟩
      rw [eval_flagVar ha x hP_fl_b.1 (by omega), hP_val]
      exact decide_eq_true hlt
    · refine ⟨(flagVar ha resH.2.flag, true), by simp [topCl], ?_⟩
      rw [eval_flagVar ha x hH_fl_b.1 hH_fl_b.2, hH_val, ← hsum_eq]
      exact decide_eq_true (by omega)
  have hsat_iff : ∀ (x : V → Bool) (y : Fin a → Bool),
      Satisfies (Sum.elim x y) (↑extra : Set (Clause (V ⊕ Fin a))) ↔ y = value a H pick x := by
    intro x y
    constructor
    · intro hsat
      rw [hval_eq x]
      apply (satisfies_tseitinAll_iff hH.1 x y).mp
      intro cl hcl
      apply hsat
      simp only [Finset.mem_coe, extra, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl hcl))
    · rintro rfl
      intro cl hcl
      simp only [Finset.mem_coe, extra, Finset.mem_union, Finset.mem_singleton] at hcl
      rcases hcl with ((h | h) | h) | rfl
      · exact (satisfies_tseitinAll_iff hH.1 x (value a H pick x)).mpr (hval_eq x) cl h
      · rw [hval_eq x]
        exact pClauses_sat hLd hw0_gt hw0_pos btP [] gs (cvalid_nil (2 + e)) hH.2.1 ha x cl h
      · rw [hval_eq x]
        exact hClauses_sat hRd hw0_gt hw0_pos btH resP.1 gs hP.1 List.prefix_rfl ha x cl h
      · exact htop_sat x

  set Ffull : Set (Clause (V ⊕ Fin a)) := Set.image (lift a) F ∪ (↑extra : Set (Clause (V ⊕ Fin a)))
  have hB_ge : max (b + 1) 3 ≤ C_up := le_max_left _ _
  have hne_p : ∀ p : Fin (n + 1), pigeonEdges G p ≠ [] := by
    intro p hnil
    have hcard0 : (G p).card = 0 := by
      have := pigeonEdges_length G p; rw [hnil] at this; simpa using this.symm
    have h1 : 1 ≤ n / s₀ := (Nat.le_div_iff_mul_le hs₀).mpr (by omega)
    have hexp := hE {p} (by rw [Finset.card_singleton]; exact h1)
    rw [Finset.card_singleton] at hexp
    have hsub : uniqueNbrs G {p} ⊆ G p := by
      intro q hq
      simp only [uniqueNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨p', hp'⟩ := Finset.card_eq_one.mp hq
      have hm : p' ∈ Finset.filter (fun i => q ∈ G i) {p} := by rw [hp']; simp
      simp only [Finset.mem_filter, Finset.mem_singleton] at hm
      exact hm.1 ▸ hm.2
    have := Finset.card_le_card hsub
    omega
  have hax_row : ∀ p : Fin (n + 1),
      ((Finset.univ.filter (fun l : Literal V => l.1.1.1 = p ∧ l.2 = true)).image
        (fun l => ((Sum.inl l.1 : V ⊕ Fin a), l.2))) ∈ Ffull := by
    intro p
    exact Or.inl ⟨_, Or.inl (Or.inl ⟨p, rfl⟩), rfl⟩
  have hax_pair : ∀ (h : Fin n) (e1 e2 : V), e1.1.2 = h → e2.1.2 = h → e1 ≠ e2 →
      ({(Sum.inl e1, false), (Sum.inl e2, false)} : Clause (V ⊕ Fin a)) ∈ Ffull := by
    intro h e1 e2 he1 he2 hne
    have hp_ne : e1.1.1 ≠ e2.1.1 := by
      intro hp
      apply hne
      apply Subtype.ext
      exact Prod.ext hp (he1.trans he2.symm)
    refine Or.inl ⟨{(e1, false), (e2, false)}, Or.inl (Or.inr ⟨e1, e2, he1.trans he2.symm, hp_ne, rfl⟩), ?_⟩
    simp [lift]
  have hP_wf : resP.2.Wf (2 + e) gs :=
    BuiltP.wf_mono (List.IsPrefix.length_le hH.2.1) hP.2.2.2.2.2.1
  obtain ⟨d1, _, hmem_P, hlen_d1⟩ := derive_pTree ha Ffull hB_ge hLd hne_p hax_row gs rfl resP.2 hP_wf
    (fun cl hcl => Or.inr (by simp [extra, hcl])) (Deriv.empty Ffull C_up)
  obtain ⟨d2, hsub2, hmem_H, hlen_d2⟩ := derive_hTree ha Ffull (by omega) hRd hax_pair gs rfl resH.2
    hH.2.2.2.2.2.1 (fun cl hcl => Or.inr (by simp [extra, hcl])) d1
  have htop_in : topCl ∈ Ffull := Or.inr (by simp [extra])
  let d3 := d2.pushAx topCl htop_in (le_trans (Finset.card_insert_le _ _) (by simp; omega))
  have hP_lt_H : resP.2.flag < resH.2.flag := by
    have h1 := hP_fl_b.2
    have h2 : 2 + e + resP.1.length ≤ resH.2.flag := hH.2.2.2.2.2.2.1
    omega
  have hPH_ne : flagVar ha resP.2.flag ≠ flagVar ha resH.2.flag :=
    flagVar_inj ha hP_fl_b.1 (by have := List.IsPrefix.length_le hH.2.1; omega) hH_fl_b.1 hH_fl_b.2 (by omega)
  have hres_top1 : IsResolvent topCl {(flagVar ha resP.2.flag, false)} {(flagVar ha resH.2.flag, true)} := by
    refine ⟨flagVar ha resP.2.flag, by simp [topCl], by simp, ?_⟩
    ext l; simp only [topCl, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro rfl; exact Or.inl ⟨by simp [hPH_ne.symm], Or.inr rfl⟩
    · rintro (⟨hn, rfl | rfl⟩ | ⟨hn, rfl⟩)
      · exact absurd rfl hn
      · rfl
      · exact absurd rfl hn
  let d4 := d3.pushRes _ _ {(flagVar ha resH.2.flag, true)}
    (by simp [d3, Deriv.pushAx]) (by simp [d3, Deriv.pushAx, hsub2 _ hmem_P]) hres_top1 (by simp; omega)
  have hres_top2 : IsResolvent
      ({(flagVar (V := V) ha resH.2.flag, true)} : Clause (V ⊕ Fin a))
      {(flagVar (V := V) ha resH.2.flag, false)} ∅ := by
    refine ⟨flagVar ha resH.2.flag, by simp, by simp, ?_⟩
    ext l; simp
  let d5 := d4.pushRes _ _ ∅
    (by simp [d4, Deriv.pushRes]) (by simp [d4, d3, Deriv.pushRes, Deriv.pushAx, hmem_H]) hres_top2 (by simp)
  refine ⟨a, extra, H, pick, hallow_H, hlen_H, ?_, hextra_width, hsat_iff, d5.lines, ⟨d5.hD, by simp [d5, Deriv.pushRes]⟩, ?_, d5.hW⟩
  · have hHsz : H.size = a := rfl
    have hC_ge : 6 * ((5 * w0 * b + 3 * b + 15 * w0 + 16) * 3 + 13 * 12) +
        (4 * b * b + 20 * b + 20) * 3 + 20 ≤ C_up := le_max_right _ _
    have h5 : 5 * a ≤ 5 * (((5 * w0 * b + 3 * b + 15 * w0 + 16) * 3 + 13 * 12) * n) :=
      Nat.mul_le_mul_left 5 hgs_bound
    have hbp : (b + 1) * (n + 1) ≤ (b + 1) * (2 * n) := Nat.mul_le_mul_left _ (by omega)
    have hrest : (b + 1) * (2 * n) + (3 * b + 3) * n + 1 ≤
        ((4 * b * b + 20 * b + 20) * 3 + 20) * n := by
      have h1 : 1 ≤ 20 * n := by omega
      have h2 : (b + 1) * (2 * n) + (3 * b + 3) * n = (5 * b + 5) * n := by ring
      have h3 : (5 * b + 5) * n ≤ ((4 * b * b + 20 * b + 20) * 3) * n :=
        Nat.mul_le_mul_right n (by omega)
      rw [h2]; calc (5 * b + 5) * n + 1 ≤ ((4 * b * b + 20 * b + 20) * 3) * n + 20 * n := by omega
        _ = ((4 * b * b + 20 * b + 20) * 3 + 20) * n := by ring
    calc a + H.size + extra.card
        ≤ 5 * a + (b + 1) * (n + 1) + (3 * b + 3) * n + 1 := by omega
      _ ≤ 5 * (((5 * w0 * b + 3 * b + 15 * w0 + 16) * 3 + 13 * 12) * n) +
          ((4 * b * b + 20 * b + 20) * 3 + 20) * n := by omega
      _ ≤ (6 * ((5 * w0 * b + 3 * b + 15 * w0 + 16) * 3 + 13 * 12) +
          (4 * b * b + 20 * b + 20) * 3 + 20) * n := by
            rw [← mul_assoc, ← add_mul]
            refine Nat.mul_le_mul_right n ?_
            rw [add_assoc (6 * _)]
            exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by decide)) _
      _ ≤ C_up * n := Nat.mul_le_mul_right n hC_ge
  · have hC_ge : 6 * ((5 * w0 * b + 3 * b + 15 * w0 + 16) * 3 + 13 * 12) +
        (4 * b * b + 20 * b + 20) * 3 + 20 ≤ C_up := le_max_right _ _
    have hd5 : d5.lines.length = d2.lines.length + 3 := by simp [d5, d4, d3, Deriv.pushRes, Deriv.pushAx]
    have hlcP : resP.2.leafCount = n + 1 := by rw [buildP_leafCount, hP_sz]
    have hlcH : resH.2.leafCount = n := by rw [buildH_leafCount, hH_sz]
    rw [hlcP] at hlen_d1
    rw [hlcH] at hlen_d2
    simp only [Deriv.empty, List.length_nil, zero_add] at hlen_d1
    have hd1_le : d1.lines.length ≤ (2 * b + 4) * (2 * n) :=
      le_trans (le_trans (Nat.le_add_right _ _) hlen_d1) (Nat.mul_le_mul_left _ (by omega))
    have hsum_le : (2 * b + 4) * (2 * n) + (4 * b * b + 12 * b + 5) * n ≤ C_up * n := by
      have h1 : (2 * b + 4) * (2 * n) + (4 * b * b + 12 * b + 5) * n =
          (4 * b * b + 16 * b + 13) * n := by ring
      rw [h1]
      exact Nat.mul_le_mul_right n (by omega)
    omega

end

end PEqualNP.Outside.L_pcx_366_aux

theorem PEqualNP.Outside.L_pcx_366 : (∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let e := Fintype.card V
    let F := PEqualNP.Expanders.funGraphPHP G
    let lift := fun (a : ℕ) (cl : PEqualNP.ProofComplexity.Clause V) =>
      cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin a), l.2))
    let allowed := fun (H : PEqualNP.CircuitLowerBounds.Circuit) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+e) H ∧
      ∀ g ∈ H.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
        g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)
    let value := fun (a : ℕ) (H : PEqualNP.CircuitLowerBounds.Circuit)
        (pick : Fin a → Fin (2+e+H.size)) (x : V → Bool) (i : Fin a) =>
      (H.wires ([false,true] ++ List.ofFn (fun j : Fin e => x ((Fintype.equivFin V).symm j)))).getD
        (pick i).val false
    (∀ (a k : ℕ) (extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin a)))
        (H : PEqualNP.CircuitLowerBounds.Circuit) (pick : Fin a → Fin (2+e+H.size)),
      1 ≤ k → allowed H →
      (∀ x : V → Bool, PEqualNP.ProofComplexity.Satisfies (Sum.elim x (value a H pick x)) extra) →
      ∀ π : List (PEqualNP.ProofComplexity.LinKLine (V ⊕ Fin a)),
        PEqualNP.ProofComplexity.IsLinKRefutation k (Set.image (lift a) F ∪ extra) π →
        let t := H.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _))
        n ≤ C^k*(t + Nat.clog 2 (π.length+1) + 1)) ∧
    ∃ (a : ℕ) (extra : Finset (PEqualNP.ProofComplexity.Clause (V ⊕ Fin a)))
        (H : PEqualNP.CircuitLowerBounds.Circuit) (pick : Fin a → Fin (2+e+H.size)),
      allowed H ∧ (∀ g ∈ H.gates, g.inputs.length ≤ 2) ∧
      a + H.size + extra.card ≤ C*n ∧ (∀ cl ∈ extra, cl.card ≤ 3) ∧
      (∀ (x : V → Bool) (y : Fin a → Bool),
        PEqualNP.ProofComplexity.Satisfies (Sum.elim x y)
          (↑extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin a))) ↔ y = value a H pick x) ∧
      ∃ π : List (PEqualNP.ProofComplexity.Clause (V ⊕ Fin a)),
        PEqualNP.ProofComplexity.IsRefutation
          (Set.image (lift a) F ∪ (↑extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin a)))) π ∧
        π.length ≤ C*n ∧ ∀ cl ∈ π, cl.card ≤ C) := by
  obtain ⟨b, s₀, n₀_43, hs₀, hG⟩ := PEqualNP.ProofComplexity.L043
  set w := max b 2
  set w0 := Nat.clog 2 (b + 1) + 1
  set C_low := 64 * (16 * s₀ * w ^ 2) * s₀ * w
  set C_up := max (max (b + 1) 3) (6 * ((5 * w0 * b + 3 * b + 15 * w0 + 16) * 3 + 13 * 12) +
    (4 * b * b + 20 * b + 20) * 3 + 20)
  set C := max (max b 2) (max C_low C_up)
  set n₀ := max n₀_43 (max (4 * (s₀ * w) + s₀) (max s₀ 1))
  refine ⟨C, n₀, by omega, fun n hn => ?_⟩
  have hn_43 : n₀_43 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 4 * (s₀ * w) + s₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn_s : s₀ ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  have hn_pos : 1 ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hn
  obtain ⟨G, hLd, hRd, hE⟩ := hG n hn_43
  have hbC : b ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hClow : C_low ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCup : C_up ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨G, fun i => le_trans (hLd i) hbC, fun j => le_trans (hRd j) hbC, ?_, ?_⟩
  · intro a k extra H pick hk hallow hsat π hπ
    exact PEqualNP.Outside.L_pcx_366_aux.lower_bound_on_expander b s₀ n hs₀ G hLd hE w rfl
      hn2 C hClow a k extra H pick hk hallow hsat π hπ
  · obtain ⟨a, extra, H, pick, hall, hlen, hsz, hwid, hiff, π, href, hplen, hpwid⟩ :=
      PEqualNP.Outside.L_pcx_366_aux.upper_bound_on_expander b s₀ n hs₀ hn_s hn_pos G hLd hRd hE
    exact ⟨a, extra, H, pick, hall, hlen, le_trans hsz (Nat.mul_le_mul_right n hCup), hwid, hiff,
      π, href, le_trans hplen (Nat.mul_le_mul_right n hCup), fun cl hcl => le_trans (hpwid cl hcl) hCup⟩

