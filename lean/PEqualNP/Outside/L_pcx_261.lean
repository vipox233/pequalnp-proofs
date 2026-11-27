import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_261_aux

open PEqualNP.ProofComplexity

private def xorPrefix (s : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => xorPrefix s k ^^ s k

private theorem xorPrefix_eq_true_iff_odd (s : ℕ → Bool) (m : ℕ) :
    xorPrefix s m = true ↔ Odd (((Finset.range m).filter (fun i => s i = true)).card) := by
  induction m with
  | zero =>
    simp [xorPrefix]
  | succ m ih =>
    have hfilt : (Finset.range (m + 1)).filter (fun i => s i = true) =
        if s m = true then insert m ((Finset.range m).filter (fun i => s i = true))
        else (Finset.range m).filter (fun i => s i = true) := by
      rw [Finset.range_add_one, Finset.filter_insert]
    have hnotmem : m ∉ (Finset.range m).filter (fun i => s i = true) := by
      simp
    rw [hfilt, xorPrefix]
    cases hsm : s m
    · simp only [Bool.false_eq_true, ite_false, Bool.xor_false]
      exact ih
    · simp only [ite_true, Finset.card_insert_of_notMem hnotmem, Bool.xor_true]
      constructor
      · intro hnot
        have hf : xorPrefix s m = false := by cases hc : xorPrefix s m <;> simp_all
        have hneven : ¬ Odd (((Finset.range m).filter (fun i => s i = true)).card) := by
          rw [← ih, hf]; decide
        rcases Nat.even_or_odd (((Finset.range m).filter (fun i => s i = true)).card) with he | ho
        · rcases he with ⟨k, hk⟩
          exact ⟨k, by omega⟩
        · exact absurd ho hneven
      · rintro ⟨k, hk⟩
        cases hc : xorPrefix s m
        · rfl
        · rcases ih.mp hc with ⟨j, hj⟩
          omega

private theorem xorPrefix_sub (s : ℕ → Bool) {i j : ℕ} (hij : i ≤ j) :
    xorPrefix s j = (xorPrefix s i ^^ xorPrefix (fun t => s (i + t)) (j - i)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero => simp [xorPrefix]
  | succ d ih =>
    have heq : i + (d + 1) = (i + d) + 1 := by omega
    rw [heq, xorPrefix, xorPrefix, ih (Nat.le_add_right i d), Bool.xor_assoc]

private def badCycle {n : ℕ} (E : Fin n → Fin n → Bool → Prop) (m : ℕ) : Prop :=
  ∃ (v : ℕ → Fin n) (s : ℕ → Bool),
    v 0 = v m ∧ Odd (((Finset.range m).filter (fun i => s i = true)).card) ∧
    ∀ i < m, E (v i) (v (i + 1)) (s i)

private def HasEdge {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u v : Fin n) (b : Bool) : Prop :=
  (u, v, b) ∈ es ∨ (v, u, b) ∈ es

private def WalkIn {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u v : Fin n) (d : ℕ) : Prop :=
  ∃ (vs : ℕ → Fin n) (ss : ℕ → Bool),
    vs 0 = u ∧ vs d = v ∧ ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)

private def Connected {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u v : Fin n) : Prop :=
  ∃ d : ℕ, WalkIn es u v d

private theorem connected_refl {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u : Fin n) :
    Connected es u u :=
  ⟨0, fun _ => u, fun _ => false, rfl, rfl, fun i hi => by omega⟩

private theorem connected_step {n : ℕ} (es : List (Fin n × Fin n × Bool)) {u v w : Fin n} {b : Bool}
    (huv : Connected es u v) (hvw : HasEdge es v w b) : Connected es u w := by
  rcases huv with ⟨d, vs, ss, hv0, hvd, hstep⟩
  refine ⟨d + 1, fun i => if i ≤ d then vs i else w, fun i => if i < d then ss i else b,
    by simp [hv0], by simp, ?_⟩
  intro i hi
  by_cases hid : i < d
  · have h1 : i ≤ d := by omega
    have h2 : i + 1 ≤ d := by omega
    simp only [h1, h2, hid, ite_true]
    exact hstep i hid
  · have hieq : i = d := by omega
    rw [hieq]
    simp only [Nat.le_refl, ite_true, show ¬ (d + 1 ≤ d) by omega, ite_false,
      show ¬ (d < d) by omega, hvd]
    exact hvw

private theorem hasEdge_symm {n : ℕ} {es : List (Fin n × Fin n × Bool)} {u v : Fin n} {b : Bool}
    (h : HasEdge es u v b) : HasEdge es v u b :=
  h.symm

private theorem walk_eval {n : ℕ} {es : List (Fin n × Fin n × Bool)} {φ : Fin n → Bool}
    (hφ : ∀ e ∈ es, (φ e.1 ^^ φ e.2.1) = e.2.2)
    {vs : ℕ → Fin n} {ss : ℕ → Bool} (d : ℕ)
    (hstep : ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)) :
    (φ (vs 0) ^^ φ (vs d)) = xorPrefix ss d := by
  induction d with
  | zero => simp [xorPrefix]
  | succ d ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    have hlast : (φ (vs d) ^^ φ (vs (d + 1))) = ss d := by
      rcases hstep d (Nat.lt_succ_self d) with h1 | h2
      · exact hφ _ h1
      · have h := hφ _ h2
        rw [Bool.xor_comm] at h
        exact h
    rw [xorPrefix, ← hprev, ← hlast]
    cases φ (vs 0) <;> cases φ (vs d) <;> cases φ (vs (d + 1)) <;> rfl

private theorem shortest_walk_nodup {n : ℕ} {es : List (Fin n × Fin n × Bool)} {u v : Fin n} {d : ℕ}
    (hmin : ∀ d' < d, ¬ WalkIn es u v d')
    {vs : ℕ → Fin n} {ss : ℕ → Bool}
    (hv0 : vs 0 = u) (hvd : vs d = v)
    (hstep : ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)) :
    ∀ p q : ℕ, p ≤ d → q ≤ d → vs p = vs q → p = q := by
  intro p q hp hq hpq
  by_contra hne
  wlog hlt : p < q generalizing p q
  · exact this q p hq hp hpq.symm (Ne.symm hne) (by omega)
  let d' := d - (q - p)
  have hd' : d' < d := by omega
  apply hmin d' hd'
  refine ⟨fun i => if i ≤ p then vs i else vs (i + (q - p)),
    fun i => if i < p then ss i else ss (i + (q - p)), ?_, ?_, ?_⟩
  · simp [hv0]
  · by_cases hdp : d' ≤ p
    · have hqd : q = d ∧ p = d' := by omega
      simp only [hdp, ite_true]
      rw [← hqd.2, hpq, hqd.1, hvd]
    · simp only [hdp, ite_false]
      have : d' + (q - p) = d := by omega
      rw [this, hvd]
  · intro i hi
    by_cases hip : i < p
    · have h1 : i ≤ p := by omega
      have h2 : i + 1 ≤ p := by omega
      simp only [h1, h2, hip, ite_true]
      exact hstep i (by omega)
    · by_cases hieq : i = p
      · subst hieq
        simp only [Nat.le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false,
          show ¬ (i < i) by omega]
        have h1 : i + 1 + (q - i) = q + 1 := by omega
        have h2 : i + (q - i) = q := by omega
        rw [h1, h2, hpq]
        exact hstep q (by omega)
      · have h1 : ¬ (i ≤ p) := by omega
        have h2 : ¬ (i + 1 ≤ p) := by omega
        have h3 : ¬ (i < p) := by omega
        simp only [h1, h2, h3, ite_false]
        have h4 : i + 1 + (q - p) = (i + (q - p)) + 1 := by omega
        rw [h4]
        exact hstep (i + (q - p)) (by omega)

private theorem shortest_walk_le_len {n : ℕ} {es : List (Fin n × Fin n × Bool)} {u v : Fin n} {d : ℕ}
    (hmin : ∀ d' < d, ¬ WalkIn es u v d')
    {vs : ℕ → Fin n} {ss : ℕ → Bool}
    (hv0 : vs 0 = u) (hvd : vs d = v)
    (hstep : ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)) :
    d ≤ es.length := by
  have hinj := shortest_walk_nodup hmin hv0 hvd hstep
  have hex : ∀ i : Fin d, ∃ k : Fin es.length,
      es[k.val] = (vs i.val, vs (i.val + 1), ss i.val) ∨
      es[k.val] = (vs (i.val + 1), vs i.val, ss i.val) := by
    intro i
    rcases hstep i.val i.isLt with h1 | h2
    · rcases List.mem_iff_getElem.mp h1 with ⟨k, hk, hget⟩
      exact ⟨⟨k, hk⟩, Or.inl hget⟩
    · rcases List.mem_iff_getElem.mp h2 with ⟨k, hk, hget⟩
      exact ⟨⟨k, hk⟩, Or.inr hget⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro i j hij
    have hi := hf i
    have hj := hf j
    rw [hij] at hi
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · have heq := hi.symm.trans hj
      have h1 : vs i.val = vs j.val := congrArg Prod.fst heq
      exact Fin.ext (hinj i.val j.val (by omega) (by omega) h1)
    · have heq := hi.symm.trans hj
      have h1 : vs i.val = vs (j.val + 1) := congrArg Prod.fst heq
      have h2 : vs (i.val + 1) = vs j.val := congrArg (fun x => x.2.1) heq
      have e1 := hinj i.val (j.val + 1) (by omega) (by omega) h1
      have e2 := hinj (i.val + 1) j.val (by omega) (by omega) h2
      omega
    · have heq := hi.symm.trans hj
      have h1 : vs (i.val + 1) = vs j.val := congrArg Prod.fst heq
      have h2 : vs i.val = vs (j.val + 1) := congrArg (fun x => x.2.1) heq
      have e1 := hinj (i.val + 1) j.val (by omega) (by omega) h1
      have e2 := hinj i.val (j.val + 1) (by omega) (by omega) h2
      omega
    · have heq := hi.symm.trans hj
      have h1 : vs (i.val + 1) = vs (j.val + 1) := congrArg Prod.fst heq
      have e1 := hinj (i.val + 1) (j.val + 1) (by omega) (by omega) h1
      exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective f hfinj
  simpa using hcard

private theorem consistent_or_bad {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (hsym : ∀ u v b, E u v b → E v u b) (es : List (Fin n × Fin n × Bool))
    (hE : ∀ e ∈ es, E e.1 e.2.1 e.2.2) :
    (∃ φ : Fin n → Bool, ∀ e ∈ es, (φ e.1 ^^ φ e.2.1) = e.2.2) ∨
    (∃ j ≤ es.length, badCycle E j) := by
  classical
  induction es with
  | nil =>
    left
    exact ⟨fun _ => false, fun _ h => by simp at h⟩
  | cons e rest ih =>
    rcases e with ⟨u, v, b⟩
    have hE_e : E u v b := hE (u, v, b) (by simp)
    have hE_rest : ∀ e' ∈ rest, E e'.1 e'.2.1 e'.2.2 := fun e' he' => hE e' (by simp [he'])
    rcases ih hE_rest with ⟨φ, hφ⟩ | ⟨j, hj, hbad⟩
    · by_cases hconn : Connected rest u v
      · by_cases hsat : (φ u ^^ φ v) = b
        · left
          refine ⟨φ, fun e' he' => ?_⟩
          simp only [List.mem_cons] at he'
          rcases he' with rfl | hr
          · exact hsat
          · exact hφ e' hr
        · right
          let d := Nat.find hconn
          have hd_walk : WalkIn rest u v d := Nat.find_spec hconn
          have hd_min : ∀ d' < d, ¬ WalkIn rest u v d' := fun d' hd' => Nat.find_min hconn hd'
          rcases hd_walk with ⟨vs, ss, hv0, hvd, hstep⟩
          have hd_le : d ≤ rest.length := shortest_walk_le_len hd_min hv0 hvd hstep
          have hpar := walk_eval hφ d hstep
          rw [hv0, hvd] at hpar
          refine ⟨d + 1, by simp; omega, ?_⟩
          let vs' : ℕ → Fin n := fun i => if i ≤ d then vs i else u
          let ss' : ℕ → Bool := fun i => if i < d then ss i else b
          refine ⟨vs', ss', by simp [vs', hv0], ?_, ?_⟩
          · rw [← xorPrefix_eq_true_iff_odd]
            have hpre : xorPrefix ss' d = xorPrefix ss d := by
              have hgen : ∀ k ≤ d, xorPrefix ss' k = xorPrefix ss k := by
                intro k hk
                induction k with
                | zero => rfl
                | succ k ihk =>
                  simp only [xorPrefix, ihk (by omega), ss', show k < d by omega, ite_true]
              exact hgen d (Nat.le_refl d)
            rw [xorPrefix, hpre]
            simp only [ss', show ¬ (d < d) by omega, ite_false]
            rw [← hpar]
            cases hc : (φ u ^^ φ v) <;> cases hb : b <;> simp_all
          · intro i hi
            by_cases hid : i < d
            · simp only [vs', ss', show i ≤ d by omega, show i + 1 ≤ d by omega, hid, ite_true]
              rcases hstep i hid with h1 | h2
              · exact hE_rest _ h1
              · exact hsym _ _ _ (hE_rest _ h2)
            · have hieq : i = d := by omega
              subst hieq
              simp only [vs', ss', Nat.le_refl, ite_true, show ¬ (d + 1 ≤ d) by omega, ite_false,
                show ¬ (d < d) by omega, hvd]
              exact hsym u v b hE_e
      · left
        let delta : Bool := (φ u ^^ φ v) ^^ b
        let φ' : Fin n → Bool := fun z => if Connected rest u z then φ z ^^ delta else φ z
        refine ⟨φ', fun e' he' => ?_⟩
        simp only [List.mem_cons] at he'
        rcases he' with rfl | hr
        · simp only [φ', connected_refl rest u, ite_true, hconn, ite_false, delta]
          cases φ u <;> cases φ v <;> cases b <;> rfl
        · rcases e' with ⟨x, y, b'⟩
          have hxy : Connected rest u x ↔ Connected rest u y :=
            ⟨fun hx => connected_step rest hx (Or.inl hr),
             fun hy => connected_step rest hy (Or.inr hr)⟩
          have hbase : (φ x ^^ φ y) = b' := hφ (x, y, b') hr
          dsimp only [φ']
          by_cases hcx : Connected rest u x
          · have hcy : Connected rest u y := hxy.mp hcx
            simp only [hcx, hcy, ite_true, ← hbase]
            cases φ x <;> cases φ y <;> cases delta <;> rfl
          · have hcy : ¬ Connected rest u y := fun h => hcx (hxy.mpr h)
            simp only [hcx, hcy, ite_false]
            exact hbase
    · right
      exact ⟨j, by simp; omega, hbad⟩

private theorem resolvent_sound {V : Type} [DecidableEq V] {φ : V → Bool} {C D R : Clause V}
    (hres : IsResolvent C D R) (hC : ClauseSat φ C) (hD : ClauseSat φ D) : ClauseSat φ R := by
  rcases hres with ⟨v, _, _, rfl⟩
  cases hv : φ v
  · rcases hC with ⟨l, hlC, hlφ⟩
    have hne : l ≠ (v, true) := by
      intro heq; subst heq; simp only at hlφ; rw [hv] at hlφ; cases hlφ
    exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlC⟩), hlφ⟩
  · rcases hD with ⟨l, hlD, hlφ⟩
    have hne : l ≠ (v, false) := by
      intro heq; subst heq; simp only at hlφ; rw [hv] at hlφ; cases hlφ
    exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlD⟩), hlφ⟩

private theorem lower_bounds {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (hsym : ∀ u v b, E u v b → E v u b)
    (g : ℕ) (hg : badCycle E g) (hmin : ∀ j < g, ¬ badCycle E j)
    (L h w : ℕ)
    (nodes inner : Finset (List Bool)) (line : List Bool → Clause (Fin n))
    (hroot : [] ∈ nodes) (hsub : inner ⊆ nodes) (hempty : line [] = ∅)
    (hbound : ∀ p ∈ nodes, p.length ≤ h ∧ (line p).card ≤ w)
    (hleaves : (nodes \ inner).card ≤ L)
    (hax : ∀ p ∈ nodes, p ∉ inner →
      ∃ (u v : Fin n) (b a : Bool), E u v b ∧ line p = {(u, !a), (v, a ^^ b)})
    (hparent : ∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ nodes → p ∈ inner)
    (hres : ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
      IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    2 * g ≤ L ∧ 2 * g ≤ 2 ^ h ∧ (if g = 1 then 1 else 2) ≤ w := by
  classical
  have hg_pos : 0 < g := by
    by_contra h0
    have hge : g = 0 := by omega
    subst hge
    rcases hg with ⟨_, _, _, hodd, _⟩
    simp at hodd
  have hroot_inner : [] ∈ inner := by
    by_contra hni
    rcases hax [] hroot hni with ⟨u, v, b, a, _, heq⟩
    rw [hempty] at heq
    have hm : (u, !a) ∈ ({(u, !a), (v, a ^^ b)} : Clause (Fin n)) := by simp
    rw [← heq] at hm
    simp at hm
  rcases hres [] hroot_inner with ⟨hF_mem, hT_mem, hroot_res⟩
  simp only [List.nil_append] at hF_mem hT_mem hroot_res
  rw [hempty] at hroot_res
  rcases hroot_res with ⟨x0, hxF, hxT, h0eq⟩
  have hF_eq : line [false] = {(x0, true)} := by
    have h1 : (line [false]).erase (x0, true) = ∅ := by
      have := Finset.union_eq_empty.mp h0eq.symm
      exact this.1
    ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have hm : l ∈ (line [false]).erase (x0, true) := Finset.mem_erase.mpr ⟨hne, hl⟩
      rw [h1] at hm; simp at hm
    · rintro rfl; exact hxF
  have hT_eq : line [true] = {(x0, false)} := by
    have h2 : (line [true]).erase (x0, false) = ∅ := by
      have := Finset.union_eq_empty.mp h0eq.symm
      exact this.2
    ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have hm : l ∈ (line [true]).erase (x0, false) := Finset.mem_erase.mpr ⟨hne, hl⟩
      rw [h2] at hm; simp at hm
    · rintro rfl; exact hxT
  let leaves := nodes \ inner
  let subL : List Bool → Finset (List Bool) := fun p => leaves.filter (fun q => p <+: q)
  have hprefix_inner : ∀ p rest : List Bool, rest ≠ [] → p ++ rest ∈ nodes → p ∈ inner := by
    intro p rest
    induction rest using List.reverseRecOn with
    | nil => intro h; exact absurd rfl h
    | append_singleton r b ih =>
      intro _ hmem
      rw [← List.append_assoc] at hmem
      have hpr := hparent (p ++ r) b hmem
      cases r with
      | nil => simpa using hpr
      | cons c cs => exact ih (by simp) (hsub hpr)
  have hsubL_leaf : ∀ p ∈ nodes, p ∉ inner → subL p = {p} := by
    intro p hp hni
    ext q
    simp only [subL, leaves, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hqn, _⟩, ⟨rest, rfl⟩⟩
      cases rest with
      | nil => simp
      | cons b bs =>
        exact absurd (hprefix_inner p (b :: bs) (by simp) hqn) hni
    · rintro rfl
      exact ⟨⟨hp, hni⟩, List.prefix_refl _⟩
  have hsubL_split : ∀ p ∈ inner, subL p = subL (p ++ [false]) ∪ subL (p ++ [true]) := by
    intro p hpi
    ext q
    simp only [subL, leaves, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hq, ⟨rest, rfl⟩⟩
      cases rest with
      | nil =>
        simp at hq
        exact absurd hpi hq.2
      | cons b bs =>
        cases b
        · left
          refine ⟨hq, ⟨bs, by simp⟩⟩
        · right
          refine ⟨hq, ⟨bs, by simp⟩⟩
    · rintro (⟨hq, ⟨rest, rfl⟩⟩ | ⟨hq, ⟨rest, rfl⟩⟩)
      · exact ⟨hq, ⟨false :: rest, by simp⟩⟩
      · exact ⟨hq, ⟨true :: rest, by simp⟩⟩
  have hsubL_card_pow : ∀ d : ℕ, ∀ p ∈ nodes, h - p.length ≤ d → (subL p).card ≤ 2 ^ d := by
    intro d
    induction d with
    | zero =>
      intro p hp hd0
      have hlen : p.length = h := by have := (hbound p hp).1; omega
      have hni : p ∉ inner := by
        intro hpi
        have hf := (hres p hpi).1
        have hfl := (hbound (p ++ [false]) hf).1
        simp [hlen] at hfl
      rw [hsubL_leaf p hp hni]
      simp
    | succ d ih =>
      intro p hp hd
      by_cases hpi : p ∈ inner
      · rcases hres p hpi with ⟨hf, ht, _⟩
        rw [hsubL_split p hpi]
        have hlen_f : (p ++ [false]).length = p.length + 1 := by simp
        have hlen_t : (p ++ [true]).length = p.length + 1 := by simp
        have h1 := ih (p ++ [false]) hf (by omega)
        have h2 := ih (p ++ [true]) ht (by omega)
        have hu := Finset.card_union_le (subL (p ++ [false])) (subL (p ++ [true]))
        rw [Nat.pow_succ]
        omega
      · rw [hsubL_leaf p hp hpi]
        simp only [Finset.card_singleton]
        exact Nat.one_le_two_pow
  have hsound : ∀ d : ℕ, ∀ p ∈ nodes, h - p.length ≤ d →
      ∀ φ : Fin n → Bool, (∀ q ∈ subL p, ClauseSat φ (line q)) → ClauseSat φ (line p) := by
    intro d
    induction d with
    | zero =>
      intro p hp hd0 φ hsat
      have hlen : p.length = h := by have := (hbound p hp).1; omega
      have hni : p ∉ inner := by
        intro hpi
        have hf := (hres p hpi).1
        have hfl := (hbound (p ++ [false]) hf).1
        simp [hlen] at hfl
      apply hsat p
      rw [hsubL_leaf p hp hni]
      simp
    | succ d ih =>
      intro p hp hd φ hsat
      by_cases hpi : p ∈ inner
      · rcases hres p hpi with ⟨hf, ht, hpr⟩
        have hsp := hsubL_split p hpi
        have hsf : ClauseSat φ (line (p ++ [false])) := by
          apply ih (p ++ [false]) hf (by simp; omega) φ
          intro q hq; exact hsat q (by rw [hsp]; exact Finset.mem_union_left _ hq)
        have hst : ClauseSat φ (line (p ++ [true])) := by
          apply ih (p ++ [true]) ht (by simp; omega) φ
          intro q hq; exact hsat q (by rw [hsp]; exact Finset.mem_union_right _ hq)
        exact resolvent_sound hpr hsf hst
      · apply hsat p
        rw [hsubL_leaf p hp hpi]
        simp
  have hunit_lb : ∀ (p : List Bool) (x : Fin n) (bit : Bool),
      p ∈ nodes → line p = {(x, bit)} → g ≤ (subL p).card := by
    intro p x bit hp hline
    have hchoose : ∀ q : List Bool, ∃ e : Fin n × Fin n × Bool,
        q ∈ subL p → E e.1 e.2.1 e.2.2 ∧ ∃ a : Bool, line q = {(e.1, !a), (e.2.1, a ^^ e.2.2)} := by
      intro q
      by_cases hq : q ∈ subL p
      · have hql : q ∈ leaves := (Finset.mem_filter.mp hq).1
        rcases Finset.mem_sdiff.mp hql with ⟨hqn, hqni⟩
        rcases hax q hqn hqni with ⟨u, v, b, a, hEuv, hqeq⟩
        exact ⟨(u, v, b), fun _ => ⟨hEuv, a, hqeq⟩⟩
      · exact ⟨(x, x, false), fun h => absurd h hq⟩
    choose f hf using hchoose
    let es := (subL p).toList.map f
    have hE_es : ∀ e ∈ es, E e.1 e.2.1 e.2.2 := by
      intro e he
      rcases List.mem_map.mp he with ⟨q, hq, rfl⟩
      exact (hf q (Finset.mem_toList.mp hq)).1
    rcases consistent_or_bad E hsym es hE_es with ⟨φ, hφ⟩ | ⟨j, hj, hbad⟩
    · exfalso
      have hsat_of : ∀ ψ : Fin n → Bool, (∀ e ∈ es, (ψ e.1 ^^ ψ e.2.1) = e.2.2) →
          ClauseSat ψ (line p) := by
        intro ψ hψ
        apply hsound h p hp (by omega) ψ
        intro q hq
        rcases (hf q hq).2 with ⟨a, hqeq⟩
        have hmem_es : f q ∈ es := List.mem_map.mpr ⟨q, Finset.mem_toList.mpr hq, rfl⟩
        have hpar := hψ (f q) hmem_es
        rw [hqeq]
        by_cases h1 : ψ (f q).1 = !a
        · exact ⟨((f q).1, !a), by simp, h1⟩
        · refine ⟨((f q).2.1, a ^^ (f q).2.2), by simp, ?_⟩
          cases hu : ψ (f q).1 <;> cases hv : ψ (f q).2.1 <;> cases ha : a <;> cases hb : (f q).2.2 <;>
            simp [hu, hv, ha, hb] at h1 hpar ⊢
      have hs1 := hsat_of φ hφ
      have hs2 := hsat_of (fun z => !(φ z)) (fun e he => by
        have h1 := hφ e he
        cases hu : φ e.1 <;> cases hv : φ e.2.1 <;> simp [hu, hv] at h1 ⊢ <;> exact h1)
      rw [hline] at hs1 hs2
      rcases hs1 with ⟨l1, hl1, h1⟩
      rcases hs2 with ⟨l2, hl2, h2⟩
      rw [Finset.mem_singleton.mp hl1] at h1
      rw [Finset.mem_singleton.mp hl2] at h2
      simp only at h1 h2
      rw [h1] at h2
      cases bit <;> simp at h2
    · have hjge : g ≤ j := by
        by_contra hlt
        exact hmin j (by omega) hbad
      have hlen : es.length = (subL p).card := by simp [es]
      omega
  have hF_lb : g ≤ (subL [false]).card := hunit_lb [false] x0 true hF_mem hF_eq
  have hT_lb : g ≤ (subL [true]).card := hunit_lb [true] x0 false hT_mem hT_eq
  have hdisj : Disjoint (subL [false]) (subL [true]) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    rcases (Finset.mem_filter.mp h1).2 with ⟨r1, hr1⟩
    rcases (Finset.mem_filter.mp h2).2 with ⟨r2, hr2⟩
    rw [← hr1] at hr2
    simp at hr2
  have hun_sub : subL [false] ∪ subL [true] ⊆ leaves := by
    intro q hq
    rcases Finset.mem_union.mp hq with h1 | h2
    · exact (Finset.mem_filter.mp h1).1
    · exact (Finset.mem_filter.mp h2).1
  have h2g_leaves : 2 * g ≤ leaves.card := by
    have h1 := Finset.card_le_card hun_sub
    rw [Finset.card_union_of_disjoint hdisj] at h1
    omega
  have hleaves_pow : leaves.card ≤ 2 ^ h := by
    have h1 := hsubL_card_pow h [] hroot (by simp)
    have h2 : subL [] = leaves := by
      ext q; simp [subL]
    rw [h2] at h1
    exact h1
  have hw_lb : (if g = 1 then 1 else 2) ≤ w := by
    split_ifs with hg1
    · have h1 := (hbound [false] hF_mem).2
      rw [hF_eq] at h1
      simpa using h1
    · have hg2 : 2 ≤ g := by omega
      by_contra hwlt
      have hw1 : w ≤ 1 := by omega
      have hne : leaves.Nonempty := Finset.card_pos.mp (by omega)
      rcases hne with ⟨q, hq⟩
      rcases Finset.mem_sdiff.mp hq with ⟨hqn, hqni⟩
      rcases hax q hqn hqni with ⟨u, v, b, a, hEuv, hqeq⟩
      have hcard := (hbound q hqn).2
      rw [hqeq] at hcard
      have heq_lit : (u, !a) = (v, a ^^ b) := by
        by_contra hne_lit
        rw [Finset.card_pair hne_lit] at hcard
        omega
      have huv : u = v := congrArg Prod.fst heq_lit
      have hab : (!a) = (a ^^ b) := congrArg Prod.snd heq_lit
      have hb : b = true := by cases a <;> cases b <;> first | rfl | cases hab
      subst huv; subst hb
      apply hmin 1 (by omega)
      refine ⟨fun _ => u, fun _ => true, rfl, ?_, fun i hi => hEuv⟩
      have : (Finset.range 1).filter (fun _ => true = true) = {0} := by decide
      rw [this]; exact ⟨0, by simp⟩
  have hL_ok : 2 * g ≤ L := h2g_leaves.trans hleaves
  have hh_ok : 2 * g ≤ 2 ^ h := h2g_leaves.trans hleaves_pow
  exact ⟨hL_ok, hh_ok, hw_lb⟩

private def chainClause {n : ℕ} (v : ℕ → Fin n) (s : ℕ → Bool) (init : Bool) (i j : ℕ) :
    Clause (Fin n) :=
  {(v i, !(init ^^ xorPrefix s i)), (v j, init ^^ xorPrefix s j)}

private def buildChain {n : ℕ} (v : ℕ → Fin n) (s : ℕ → Bool) (init : Bool) (i : ℕ) :
    (len : ℕ) → Finset (List Bool) × Finset (List Bool) × (List Bool → Clause (Fin n))
  | 0 => ({[]}, ∅, fun _ => chainClause v s init i i)
  | 1 => ({[]}, ∅, fun _ => chainClause v s init i (i + 1))
  | len + 2 =>
    let total := len + 2
    let l1 := total / 2
    let l2 := total - l1
    let k := i + l1
    have hl1 : l1 < total := by omega
    have hl2 : l2 < total := by omega
    let T1 := buildChain v s init i l1
    let T2 := buildChain v s init k l2
    let Ltree := if (init ^^ xorPrefix s k) = true then T1 else T2
    let Rtree := if (init ^^ xorPrefix s k) = true then T2 else T1
    (insert [] (Ltree.1.image (false :: ·) ∪ Rtree.1.image (true :: ·)),
     insert [] (Ltree.2.1.image (false :: ·) ∪ Rtree.2.1.image (true :: ·)),
     fun p => match p with
       | [] => chainClause v s init i (i + total)
       | false :: rest => Ltree.2.2 rest
       | true :: rest => Rtree.2.2 rest)
termination_by len => len

private theorem buildChain_spec {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (v : ℕ → Fin n) (s : ℕ → Bool) (g : ℕ)
    (hmin : ∀ j < g, ¬ badCycle E j)
    (hE : ∀ i < g, E (v i) (v (i + 1)) (s i))
    (init : Bool) :
    ∀ len : ℕ, 1 ≤ len → ∀ i : ℕ, i + len ≤ g →
      let T := buildChain v s init i len
      [] ∈ T.1 ∧
      T.2.1 ⊆ T.1 ∧
      T.2.2 [] = chainClause v s init i (i + len) ∧
      (T.1 \ T.2.1).card = len ∧
      (∀ d : ℕ, len ≤ 2 ^ d → ∀ p ∈ T.1, p.length ≤ d) ∧
      (∀ p ∈ T.1, (T.2.2 p).card ≤ (if len = 1 then (chainClause v s init i (i + 1)).card else 2)) ∧
      (∀ p ∈ T.1, p ∉ T.2.1 →
        ∃ (u u' : Fin n) (b a : Bool), E u u' b ∧ T.2.2 p = {(u, !a), (u', a ^^ b)}) ∧
      (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ T.1 → p ∈ T.2.1) ∧
      (∀ p ∈ T.2.1, p ++ [false] ∈ T.1 ∧ p ++ [true] ∈ T.1 ∧
        IsResolvent (T.2.2 (p ++ [false])) (T.2.2 (p ++ [true])) (T.2.2 p)) := by
  intro len
  induction len using Nat.strong_induction_on with
  | ind len ih =>
    intro hlen1 i hile
    match len with
    | 0 => omega
    | 1 =>
      have h1_eq : buildChain v s init i 1 = ({[]}, ∅, fun _ => chainClause v s init i (i + 1)) := by
        conv_lhs => rw [buildChain]
      rw [h1_eq]
      dsimp only
      refine ⟨by simp, by simp, rfl, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro d _ p hp
        rw [Finset.mem_singleton.mp hp]; simp
      · intro p _
        simp
      · intro p hp _
        refine ⟨v i, v (i + 1), s i, init ^^ xorPrefix s i, hE i (by omega), ?_⟩
        simp only [chainClause, xorPrefix, Bool.xor_assoc]
      · intro p bit hp
        rw [Finset.mem_singleton] at hp
        have hlen0 := congrArg List.length hp
        simp at hlen0
      · intro p hp; simp at hp
    | len' + 2 =>
      set total := len' + 2
      set l1 := total / 2
      set l2 := total - l1
      set k := i + l1
      have hl1_pos : 1 ≤ l1 := by omega
      have hl2_pos : 1 ≤ l2 := by omega
      have hl1_lt : l1 < total := by omega
      have hl2_lt : l2 < total := by omega
      have hspec1 := ih l1 hl1_lt hl1_pos i (by omega)
      have hspec2 := ih l2 hl2_lt hl2_pos k (by omega)
      set T1 := buildChain v s init i l1
      set T2 := buildChain v s init k l2
      set c := init ^^ xorPrefix s k
      set Ltree := if c = true then T1 else T2
      set Rtree := if c = true then T2 else T1
      have hL_spec : [] ∈ Ltree.1 ∧ Ltree.2.1 ⊆ Ltree.1 ∧
          (∀ p ∈ Ltree.1, p ∉ Ltree.2.1 →
            ∃ (u u' : Fin n) (b a : Bool), E u u' b ∧ Ltree.2.2 p = {(u, !a), (u', a ^^ b)}) ∧
          (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ Ltree.1 → p ∈ Ltree.2.1) ∧
          (∀ p ∈ Ltree.2.1, p ++ [false] ∈ Ltree.1 ∧ p ++ [true] ∈ Ltree.1 ∧
            IsResolvent (Ltree.2.2 (p ++ [false])) (Ltree.2.2 (p ++ [true])) (Ltree.2.2 p)) := by
        dsimp only [Ltree]; split_ifs
        · exact ⟨hspec1.1, hspec1.2.1, hspec1.2.2.2.2.2.2.1, hspec1.2.2.2.2.2.2.2.1, hspec1.2.2.2.2.2.2.2.2⟩
        · exact ⟨hspec2.1, hspec2.2.1, hspec2.2.2.2.2.2.2.1, hspec2.2.2.2.2.2.2.2.1, hspec2.2.2.2.2.2.2.2.2⟩
      have hR_spec : [] ∈ Rtree.1 ∧ Rtree.2.1 ⊆ Rtree.1 ∧
          (∀ p ∈ Rtree.1, p ∉ Rtree.2.1 →
            ∃ (u u' : Fin n) (b a : Bool), E u u' b ∧ Rtree.2.2 p = {(u, !a), (u', a ^^ b)}) ∧
          (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ Rtree.1 → p ∈ Rtree.2.1) ∧
          (∀ p ∈ Rtree.2.1, p ++ [false] ∈ Rtree.1 ∧ p ++ [true] ∈ Rtree.1 ∧
            IsResolvent (Rtree.2.2 (p ++ [false])) (Rtree.2.2 (p ++ [true])) (Rtree.2.2 p)) := by
        dsimp only [Rtree]; split_ifs
        · exact ⟨hspec2.1, hspec2.2.1, hspec2.2.2.2.2.2.2.1, hspec2.2.2.2.2.2.2.2.1, hspec2.2.2.2.2.2.2.2.2⟩
        · exact ⟨hspec1.1, hspec1.2.1, hspec1.2.2.2.2.2.2.1, hspec1.2.2.2.2.2.2.2.1, hspec1.2.2.2.2.2.2.2.2⟩
      have hT_eq : buildChain v s init i total =
          (insert [] (Ltree.1.image (false :: ·) ∪ Rtree.1.image (true :: ·)),
           insert [] (Ltree.2.1.image (false :: ·) ∪ Rtree.2.1.image (true :: ·)),
           fun p => match p with
             | [] => chainClause v s init i (i + total)
             | false :: rest => Ltree.2.2 rest
             | true :: rest => Rtree.2.2 rest) := by
        conv_lhs => rw [buildChain]
      rw [hT_eq]
      dsimp only
      have hno_bad_ik : (v i, !(init ^^ xorPrefix s i)) ≠ (v k, init ^^ xorPrefix s k) := by
        intro heq
        have hvv : v i = v k := congrArg Prod.fst heq
        have hbb : (!(init ^^ xorPrefix s i)) = (init ^^ xorPrefix s k) := congrArg Prod.snd heq
        have hsub := xorPrefix_sub s (by omega : i ≤ k)
        have hxor_t : xorPrefix (fun t => s (i + t)) (k - i) = true := by
          rw [hsub] at hbb
          cases init <;> cases xorPrefix s i <;> cases hx : xorPrefix (fun t => s (i + t)) (k - i) <;>
            simp [hx] at hbb ⊢
        apply hmin (k - i) (by omega)
        refine ⟨fun t => v (i + t), fun t => s (i + t), ?_,
          (xorPrefix_eq_true_iff_odd _ _).mp hxor_t, fun t ht => ?_⟩
        · simp only [Nat.add_zero, show i + (k - i) = k by omega, hvv]
        · dsimp only
          have hadd : i + (t + 1) = (i + t) + 1 := by omega
          rw [hadd]
          exact hE (i + t) (by omega)
      have hno_bad_kj : (v (i + total), init ^^ xorPrefix s (i + total)) ≠
          (v k, !(init ^^ xorPrefix s k)) := by
        intro heq
        have hvv : v (i + total) = v k := congrArg Prod.fst heq
        have hbb : (init ^^ xorPrefix s (i + total)) = (!(init ^^ xorPrefix s k)) := congrArg Prod.snd heq
        have hsub := xorPrefix_sub s (by omega : k ≤ i + total)
        have hxor_t : xorPrefix (fun t => s (k + t)) (i + total - k) = true := by
          rw [hsub] at hbb
          cases init <;> cases xorPrefix s k <;> cases hx : xorPrefix (fun t => s (k + t)) (i + total - k) <;>
            simp [hx] at hbb ⊢
        apply hmin (i + total - k) (by omega)
        refine ⟨fun t => v (k + t), fun t => s (k + t), ?_,
          (xorPrefix_eq_true_iff_odd _ _).mp hxor_t, fun t ht => ?_⟩
        · simp only [Nat.add_zero, show k + (i + total - k) = i + total by omega, hvv]
        · dsimp only
          have hadd : k + (t + 1) = (k + t) + 1 := by omega
          rw [hadd]
          exact hE (k + t) (by omega)
      have hroot_res : IsResolvent (Ltree.2.2 []) (Rtree.2.2 []) (chainClause v s init i (i + total)) := by
        refine ⟨v k, ?_, ?_, ?_⟩
        · dsimp only [Ltree]; split_ifs with hc
          · rw [hspec1.2.2.1]; simp [chainClause, k, c, hc]
          · rw [hspec2.2.2.1]
            have hcf : c = false := by cases hc' : c <;> simp_all
            simp [chainClause, c, hcf]
        · dsimp only [Rtree]; split_ifs with hc
          · rw [hspec2.2.2.1]; simp [chainClause, c, hc]
          · rw [hspec1.2.2.1]
            have hcf : c = false := by cases hc' : c <;> simp_all
            simp [chainClause, k, c, hcf]
        · have hk_add : k + l2 = i + total := by omega
          have he1 : (chainClause v s init i k).erase (v k, init ^^ xorPrefix s k) =
              {(v i, !(init ^^ xorPrefix s i))} := by
            unfold chainClause
            ext x
            simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hne, rfl | rfl⟩
              · rfl
              · exact absurd rfl hne
            · rintro rfl
              exact ⟨hno_bad_ik, Or.inl rfl⟩
          have he2 : (chainClause v s init k (i + total)).erase (v k, !(init ^^ xorPrefix s k)) =
              {(v (i + total), init ^^ xorPrefix s (i + total))} := by
            unfold chainClause
            ext x
            simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hne, rfl | rfl⟩
              · exact absurd rfl hne
              · rfl
            · rintro rfl
              exact ⟨hno_bad_kj, Or.inr rfl⟩
          dsimp only [Ltree, Rtree]
          split_ifs with hc
          · rw [hspec1.2.2.1, hspec2.2.2.1, hk_add]
            have hcf : (!c) = false := by rw [hc]; rfl
            rw [← hc, ← hcf]
            have h1 : (chainClause v s init i k).erase (v k, c) = {(v i, !(init ^^ xorPrefix s i))} := he1
            have h2 : (chainClause v s init k (i + total)).erase (v k, !c) =
                {(v (i + total), init ^^ xorPrefix s (i + total))} := he2
            rw [h1, h2]
            ext x; simp [chainClause]
          · have hcf : c = false := by cases hc' : c <;> simp_all
            rw [hspec1.2.2.1, hspec2.2.2.1, hk_add]
            have hct : (!c) = true := by rw [hcf]; rfl
            rw [← hct, ← hcf]
            have h1 : (chainClause v s init i k).erase (v k, c) = {(v i, !(init ^^ xorPrefix s i))} := he1
            have h2 : (chainClause v s init k (i + total)).erase (v k, !c) =
                {(v (i + total), init ^^ xorPrefix s (i + total))} := he2
            rw [h1, h2]
            ext x; simp [chainClause, or_comm]
      have hleaves_eq : (insert [] (Ltree.1.image (false :: ·) ∪ Rtree.1.image (true :: ·))) \
          (insert [] (Ltree.2.1.image (false :: ·) ∪ Rtree.2.1.image (true :: ·))) =
          (Ltree.1 \ Ltree.2.1).image (false :: ·) ∪ (Rtree.1 \ Rtree.2.1).image (true :: ·) := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        cases p with
        | nil => simp
        | cons b rest =>
          cases b <;> simp
      refine ⟨Finset.mem_insert_self _ _, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨q, hL_spec.2.1 hq, rfl⟩)
        · exact Or.inr (Or.inr ⟨q, hR_spec.2.1 hq, rfl⟩)
      · rw [hleaves_eq]
        have hdisj : Disjoint ((Ltree.1 \ Ltree.2.1).image (false :: ·))
            ((Rtree.1 \ Rtree.2.1).image (true :: ·)) := by
          rw [Finset.disjoint_left]
          intro p h1 h2
          rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨_, _, heq⟩
          cases heq
        rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
          Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2)]
        have hlc : (Ltree.1 \ Ltree.2.1).card + (Rtree.1 \ Rtree.2.1).card = l1 + l2 := by
          dsimp only [Ltree, Rtree]; split_ifs
          · rw [hspec1.2.2.2.1, hspec2.2.2.2.1]
          · rw [hspec2.2.2.2.1, hspec1.2.2.2.1]; omega
        omega
      · intro d hd p hp
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · simp
        · have hd1 : 1 ≤ d := by
            by_contra h0; have : d = 0 := by omega
            subst this; simp at hd; omega
          have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
            cases d with | zero => omega | succ d' => simp [Nat.pow_succ, Nat.mul_comm]
          have hle1 : l1 ≤ 2 ^ (d - 1) := by omega
          have hle2 : l2 ≤ 2 ^ (d - 1) := by omega
          have hqlen : q.length ≤ d - 1 := by
            dsimp only [Ltree] at hq; split_ifs at hq
            · exact hspec1.2.2.2.2.1 (d - 1) hle1 q hq
            · exact hspec2.2.2.2.2.1 (d - 1) hle2 q hq
          simp; omega
        · have hd1 : 1 ≤ d := by
            by_contra h0; have : d = 0 := by omega
            subst this; simp at hd; omega
          have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
            cases d with | zero => omega | succ d' => simp [Nat.pow_succ, Nat.mul_comm]
          have hle1 : l1 ≤ 2 ^ (d - 1) := by omega
          have hle2 : l2 ≤ 2 ^ (d - 1) := by omega
          have hqlen : q.length ≤ d - 1 := by
            dsimp only [Rtree] at hq; split_ifs at hq
            · exact hspec2.2.2.2.2.1 (d - 1) hle2 q hq
            · exact hspec1.2.2.2.2.1 (d - 1) hle1 q hq
          simp; omega
      · intro p hp
        have hne1 : total ≠ 1 := by omega
        simp only [hne1, ite_false]
        have hpair_le : ∀ a b : Literal (Fin n), ({a, b} : Clause (Fin n)).card ≤ 2 := fun a b =>
          (Finset.card_insert_le _ _).trans (by simp)
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · exact hpair_le _ _
        · dsimp only [Ltree] at hq ⊢; split_ifs at hq ⊢
          · have hc1 := hspec1.2.2.2.2.2.1 q hq
            split_ifs at hc1
            · exact hc1.trans (hpair_le _ _)
            · exact hc1
          · have hc2 := hspec2.2.2.2.2.2.1 q hq
            split_ifs at hc2
            · exact hc2.trans (hpair_le _ _)
            · exact hc2
        · dsimp only [Rtree] at hq ⊢; split_ifs at hq ⊢
          · have hc2 := hspec2.2.2.2.2.2.1 q hq
            split_ifs at hc2
            · exact hc2.trans (hpair_le _ _)
            · exact hc2
          · have hc1 := hspec1.2.2.2.2.2.1 q hq
            split_ifs at hc1
            · exact hc1.trans (hpair_le _ _)
            · exact hc1
      · intro p hp hni
        have hpm : p ∈ (Ltree.1 \ Ltree.2.1).image (false :: ·) ∪ (Rtree.1 \ Rtree.2.1).image (true :: ·) := by
          rw [← hleaves_eq]; exact Finset.mem_sdiff.mpr ⟨hp, hni⟩
        rcases Finset.mem_union.mp hpm with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨q, hq, rfl⟩
          rcases Finset.mem_sdiff.mp hq with ⟨hq1, hq2⟩
          exact hL_spec.2.2.1 q hq1 hq2
        · rcases Finset.mem_image.mp h2 with ⟨q, hq, rfl⟩
          rcases Finset.mem_sdiff.mp hq with ⟨hq1, hq2⟩
          exact hR_spec.2.2.1 q hq1 hq2
      · intro p bit hp
        cases p with
        | nil => exact Finset.mem_insert_self _ _
        | cons b rest =>
          simp only [List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
          cases b
          · simp only [reduceCtorEq, false_or] at hp
            rcases hp with ⟨q, hq, heq⟩ | ⟨q, _, heq⟩
            · have hqeq : q = rest ++ [bit] := (List.cons.inj heq).2
              subst hqeq
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨rest, hL_spec.2.2.2.1 rest bit hq, rfl⟩))
            · cases heq
          · simp only [reduceCtorEq, false_or] at hp
            rcases hp with ⟨q, _, heq⟩ | ⟨q, hq, heq⟩
            · cases heq
            · have hqeq : q = rest ++ [bit] := (List.cons.inj heq).2
              subst hqeq
              exact Finset.mem_insert_of_mem (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨rest, hR_spec.2.2.2.1 rest bit hq, rfl⟩))
      · intro p hp
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
        · simp only [List.nil_append]
          refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[], hL_spec.1, rfl⟩)),
            Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨[], hR_spec.1, rfl⟩)),
            hroot_res⟩
        · rcases hL_spec.2.2.2.2 q hq with ⟨hf, ht, hr⟩
          simp only [List.cons_append]
          refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [false], hf, rfl⟩)),
            Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [true], ht, rfl⟩)),
            hr⟩
        · rcases hR_spec.2.2.2.2 q hq with ⟨hf, ht, hr⟩
          simp only [List.cons_append]
          refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [false], hf, rfl⟩)),
            Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [true], ht, rfl⟩)),
            hr⟩

private theorem upper_construction {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (g : ℕ) (hg : badCycle E g) (hmin : ∀ j < g, ¬ badCycle E j)
    (L h w : ℕ) (hL : 2 * g ≤ L) (hh : 2 * g ≤ 2 ^ h) (hw : (if g = 1 then 1 else 2) ≤ w) :
    ∃ (nodes inner : Finset (List Bool)) (line : List Bool → Clause (Fin n)),
      [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
      (∀ p ∈ nodes, p.length ≤ h ∧ (line p).card ≤ w) ∧
      (nodes \ inner).card ≤ L ∧
      (∀ p ∈ nodes, p ∉ inner →
        ∃ (u v : Fin n) (b a : Bool), E u v b ∧ line p = {(u, !a), (v, a ^^ b)}) ∧
      (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ nodes → p ∈ inner) ∧
      ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
        IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p) := by
  rcases hg with ⟨v, s, hv, hodd, hE⟩
  have hg_pos : 1 ≤ g := by
    by_contra h0; have : g = 0 := by omega
    subst this; simp at hodd
  have hpar_g : xorPrefix s g = true := (xorPrefix_eq_true_iff_odd s g).mpr hodd
  have hcl_false : chainClause v s false 0 g = {(v 0, true)} := by
    simp [chainClause, xorPrefix, hpar_g, hv]
  have hcl_true : chainClause v s true 0 g = {(v 0, false)} := by
    simp [chainClause, xorPrefix, hpar_g, hv]
  have hspecF := buildChain_spec E v s g hmin hE false g hg_pos 0 (by omega)
  have hspecT := buildChain_spec E v s g hmin hE true g hg_pos 0 (by omega)
  set TF := buildChain v s false 0 g
  set TT := buildChain v s true 0 g
  let nodes := insert ([] : List Bool) (TF.1.image (false :: ·) ∪ TT.1.image (true :: ·))
  let inner := insert ([] : List Bool) (TF.2.1.image (false :: ·) ∪ TT.2.1.image (true :: ·))
  let line : List Bool → Clause (Fin n) := fun p =>
    match p with
    | [] => ∅
    | false :: rest => TF.2.2 rest
    | true :: rest => TT.2.2 rest
  have hleaves_eq : nodes \ inner =
      (TF.1 \ TF.2.1).image (false :: ·) ∪ (TT.1 \ TT.2.1).image (true :: ·) := by
    ext p
    simp only [nodes, inner, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    cases p with
    | nil => simp
    | cons b rest => cases b <;> simp
  have hh1 : 1 ≤ h := by
    by_contra h0; have : h = 0 := by omega
    subst this; simp at hh; omega
  have hg_pow : g ≤ 2 ^ (h - 1) := by
    have hpow : 2 ^ h = 2 * 2 ^ (h - 1) := by
      cases h with | zero => omega | succ h' => simp [Nat.pow_succ, Nat.mul_comm]
    omega
  refine ⟨nodes, inner, line, Finset.mem_insert_self _ _, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [nodes, inner, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨q, hspecF.2.1 hq, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, hspecT.2.1 hq, rfl⟩)
  · intro p hp
    simp only [nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨by simp, by simp [line]⟩
    · refine ⟨?_, ?_⟩
      · have hql := hspecF.2.2.2.2.1 (h - 1) hg_pow q hq
        simp; omega
      · have hqc := hspecF.2.2.2.2.2.1 q hq
        simp only [Nat.zero_add] at hqc
        split_ifs at hqc with hg1
        · subst hg1
          rw [hcl_false] at hqc
          simp only [Finset.card_singleton] at hqc
          simp only [ite_true] at hw
          exact hqc.trans hw
        · simp only [hg1, ite_false] at hw
          exact hqc.trans hw
    · refine ⟨?_, ?_⟩
      · have hql := hspecT.2.2.2.2.1 (h - 1) hg_pow q hq
        simp; omega
      · have hqc := hspecT.2.2.2.2.2.1 q hq
        simp only [Nat.zero_add] at hqc
        split_ifs at hqc with hg1
        · subst hg1
          rw [hcl_true] at hqc
          simp only [Finset.card_singleton] at hqc
          simp only [ite_true] at hw
          exact hqc.trans hw
        · simp only [hg1, ite_false] at hw
          exact hqc.trans hw
  · rw [hleaves_eq]
    have hdisj : Disjoint ((TF.1 \ TF.2.1).image (false :: ·)) ((TT.1 \ TT.2.1).image (true :: ·)) := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨_, _, heq⟩
      cases heq
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
      Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
      hspecF.2.2.2.1, hspecT.2.2.2.1]
    omega
  · intro p hp hni
    have hpm : p ∈ (TF.1 \ TF.2.1).image (false :: ·) ∪ (TT.1 \ TT.2.1).image (true :: ·) := by
      rw [← hleaves_eq]; exact Finset.mem_sdiff.mpr ⟨hp, hni⟩
    rcases Finset.mem_union.mp hpm with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨q, hq, rfl⟩
      rcases Finset.mem_sdiff.mp hq with ⟨hq1, hq2⟩
      exact hspecF.2.2.2.2.2.2.1 q hq1 hq2
    · rcases Finset.mem_image.mp h2 with ⟨q, hq, rfl⟩
      rcases Finset.mem_sdiff.mp hq with ⟨hq1, hq2⟩
      exact hspecT.2.2.2.2.2.2.1 q hq1 hq2
  · intro p bit hp
    cases p with
    | nil => exact Finset.mem_insert_self _ _
    | cons b rest =>
      simp only [nodes, List.cons_append, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      cases b
      · simp only [reduceCtorEq, false_or] at hp
        rcases hp with ⟨q, hq, heq⟩ | ⟨q, _, heq⟩
        · have hqeq : q = rest ++ [bit] := (List.cons.inj heq).2
          subst hqeq
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨rest, hspecF.2.2.2.2.2.2.2.1 rest bit hq, rfl⟩))
        · cases heq
      · simp only [reduceCtorEq, false_or] at hp
        rcases hp with ⟨q, _, heq⟩ | ⟨q, hq, heq⟩
        · cases heq
        · have hqeq : q = rest ++ [bit] := (List.cons.inj heq).2
          subst hqeq
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨rest, hspecT.2.2.2.2.2.2.2.1 rest bit hq, rfl⟩))
  · intro p hp
    simp only [inner, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp only [List.nil_append]
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[], hspecF.1, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨[], hspecT.1, rfl⟩)),
        ?_⟩
      refine ⟨v 0, ?_, ?_, ?_⟩
      · dsimp only [line]; rw [hspecF.2.2.1]; simp only [Nat.zero_add, hcl_false]; simp
      · dsimp only [line]; rw [hspecT.2.2.1]; simp only [Nat.zero_add, hcl_true]; simp
      · dsimp only [line]; rw [hspecF.2.2.1, hspecT.2.2.1]; simp only [Nat.zero_add, hcl_false, hcl_true]
        simp
    · rcases hspecF.2.2.2.2.2.2.2.2 q hq with ⟨hf, ht, hr⟩
      simp only [List.cons_append]
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [false], hf, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [true], ht, rfl⟩)),
        hr⟩
    · rcases hspecT.2.2.2.2.2.2.2.2 q hq with ⟨hf, ht, hr⟩
      simp only [List.cons_append]
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [false], hf, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [true], ht, rfl⟩)),
        hr⟩

end PEqualNP.Outside.L_pcx_261_aux

theorem PEqualNP.Outside.L_pcx_261 :
∀ (n : ℕ) (E : Fin n → Fin n → Bool → Prop),
  (∀ u v b, E u v b → E v u b) →
  let bad := fun m : ℕ => ∃ (v : ℕ → Fin n) (s : ℕ → Bool),
    v 0 = v m ∧ Odd (((Finset.range m).filter (fun i => s i = true)).card) ∧
    ∀ i < m, E (v i) (v (i+1)) (s i)
  let ax := fun C : PEqualNP.ProofComplexity.Clause (Fin n) =>
    ∃ (u v : Fin n) (b a : Bool), E u v b ∧ C = {(u,!a),(v,a ^^ b)}
  ∀ g : ℕ, bad g → (∀ j < g, ¬ bad j) →
    ∀ L h w : ℕ,
      (∃ (nodes inner : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause (Fin n)),
        [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
        (∀ p ∈ nodes, p.length ≤ h ∧ (line p).card ≤ w) ∧
        (nodes \ inner).card ≤ L ∧ (∀ p ∈ nodes, p ∉ inner → ax (line p)) ∧
        (∀ (p : List Bool) (bit : Bool), p ++ [bit] ∈ nodes → p ∈ inner) ∧
        ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
          PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) ↔
      2*g ≤ L ∧ 2*g ≤ 2^h ∧ (if g = 1 then 1 else 2) ≤ w := by
  intro n E hsym bad ax g hg hmin L h w
  constructor
  · rintro ⟨nodes, inner, line, hroot, hsub, hempty, hbound, hleaves, hax, hparent, hres⟩
    exact PEqualNP.Outside.L_pcx_261_aux.lower_bounds E hsym g hg hmin L h w nodes inner line
      hroot hsub hempty hbound hleaves hax hparent hres
  · rintro ⟨hL, hh, hw⟩
    exact PEqualNP.Outside.L_pcx_261_aux.upper_construction E g hg hmin L h w hL hh hw
