import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1147

-- ============================================================================
-- Section 1: Hypergraph Definitions
-- ============================================================================

noncomputable def closedB {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a)) : Bool :=
  J.toList.all (fun i => (Finset.univ : Finset (Fin a)).toList.all
    (fun h => !(decide (bank i ∩ bank h).Nonempty) || decide (h ∈ J)))

noncomputable def componentsB {n a : Nat} (bank : Fin a → Finset (Fin n)) : Finset (Finset (Fin a)) :=
  (Finset.univ : Finset (Fin a)).powerset.filter (fun J => J.Nonempty ∧ closedB bank J = true ∧
    ∀ K ∈ J.powerset, K.Nonempty → closedB bank K = true → K = J)

def supportB {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a)) : Finset (Fin n) :=
  J.biUnion bank

noncomputable def treesB {n a : Nat} (bank : Fin a → Finset (Fin n)) : Finset (Finset (Fin a)) :=
  (componentsB bank).filter (fun J =>
    J.sum (fun i => (bank i).card) + 1 = J.card + (supportB bank J).card)

def widthGCDB {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a)) : Nat :=
  J.gcd (fun i => (bank i).card)

noncomputable def badB {n a : Nat} (bank : Fin a → Finset (Fin n)) : Finset (Finset (Fin a)) :=
  (treesB bank).filter (fun J => 1 < widthGCDB bank J)

noncomputable def evenBadB {n a : Nat} (bank : Fin a → Finset (Fin n)) : Finset (Finset (Fin a)) :=
  (badB bank).filter (fun J => widthGCDB bank J % 2 = 0)

def canRecoverB {n : Nat} (a : Nat) (bank : Fin a → Finset (Fin n)) : Prop :=
  let patterns := (Finset.univ : Finset (Fin a → Finset (Fin n))).filter
    (fun p => ∀ i, p i ⊆ bank i)
  ∀ z : Finset (Fin n), ∃ c : (Fin a → Finset (Fin n)) → Int, ∀ x : Finset (Fin n),
    (patterns.filter (fun p => ∀ i, x ∩ bank i ≠ p i)).sum c =
      (if x = z then (1 : Int) else 0)

lemma closedB_iff {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a)) :
    closedB bank J = true ↔ ∀ i ∈ J, ∀ h : Fin a, (bank i ∩ bank h).Nonempty → h ∈ J := by
  unfold closedB
  simp only [List.all_eq_true, Finset.mem_toList, Finset.mem_univ, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · intro h i hi j hj
    rcases h i hi j with h1 | h2
    · exact False.elim (h1 hj)
    · exact h2
  · intro h i hi j
    by_cases hj : (bank i ∩ bank j).Nonempty
    · exact Or.inr (h i hi j hj)
    · exact Or.inl hj

-- ============================================================================
-- Section 2: Connectedness and Component Partition
-- ============================================================================

def AdjB {n a : Nat} (bank : Fin a → Finset (Fin n)) (i h : Fin a) : Prop :=
  (bank i ∩ bank h).Nonempty

lemma AdjB_symm {n a : Nat} {bank : Fin a → Finset (Fin n)} {i h : Fin a}
    (hih : AdjB bank i h) : AdjB bank h i := by
  simpa [AdjB, Finset.inter_comm] using hih

def ReachB {n a : Nat} (bank : Fin a → Finset (Fin n)) : Fin a → Fin a → Prop :=
  Relation.ReflTransGen (AdjB bank)

lemma ReachB_refl {n a : Nat} (bank : Fin a → Finset (Fin n)) (i : Fin a) :
    ReachB bank i i := Relation.ReflTransGen.refl

lemma ReachB_trans {n a : Nat} {bank : Fin a → Finset (Fin n)} {i j k : Fin a}
    (h1 : ReachB bank i j) (h2 : ReachB bank j k) : ReachB bank i k :=
  Relation.ReflTransGen.trans h1 h2

lemma ReachB_symm {n a : Nat} {bank : Fin a → Finset (Fin n)} {i j : Fin a}
    (h : ReachB bank i j) : ReachB bank j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.head (AdjB_symm hstep) ih

noncomputable def compOf {n a : Nat} (bank : Fin a → Finset (Fin n)) (i : Fin a) : Finset (Fin a) :=
  by
    classical
    exact Finset.univ.filter (fun h => ReachB bank i h)

lemma mem_compOf {n a : Nat} (bank : Fin a → Finset (Fin n)) (i h : Fin a) :
    h ∈ compOf bank i ↔ ReachB bank i h := by
  classical
  simp [compOf]

lemma self_mem_compOf {n a : Nat} (bank : Fin a → Finset (Fin n)) (i : Fin a) :
    i ∈ compOf bank i :=
  (mem_compOf bank i i).2 (ReachB_refl bank i)

lemma compOf_eq_of_reach {n a : Nat} (bank : Fin a → Finset (Fin n)) {i j : Fin a}
    (h : ReachB bank i j) : compOf bank i = compOf bank j := by
  ext k
  simp only [mem_compOf]
  exact ⟨fun hik => ReachB_trans (ReachB_symm h) hik, fun hjk => ReachB_trans h hjk⟩

lemma closedB_reach {n a : Nat} {bank : Fin a → Finset (Fin n)} {J : Finset (Fin a)}
    (hJ : closedB bank J = true) {i j : Fin a} (hi : i ∈ J) (h : ReachB bank i j) : j ∈ J := by
  have hc := (closedB_iff bank J).1 hJ
  induction h with
  | refl => exact hi
  | tail _ hstep ih => exact hc _ ih _ hstep

lemma compOf_closedB {n a : Nat} (bank : Fin a → Finset (Fin n)) (i : Fin a) :
    closedB bank (compOf bank i) = true := by
  rw [closedB_iff]
  intro u hu h huh
  rw [mem_compOf] at hu ⊢
  exact Relation.ReflTransGen.tail hu huh

lemma compOf_mem_componentsB {n a : Nat} (bank : Fin a → Finset (Fin n)) (i : Fin a) :
    compOf bank i ∈ componentsB bank := by
  rw [componentsB, Finset.mem_filter]
  refine ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ⟨i, self_mem_compOf bank i⟩,
    compOf_closedB bank i, ?_⟩
  intro K hK hKne hKcl
  have hKsub : K ⊆ compOf bank i := Finset.mem_powerset.1 hK
  rcases hKne with ⟨x, hx⟩
  have hix : ReachB bank i x := (mem_compOf bank i x).1 (hKsub hx)
  apply Finset.Subset.antisymm hKsub
  intro y hy
  have hiy : ReachB bank i y := (mem_compOf bank i y).1 hy
  exact closedB_reach hKcl hx (ReachB_trans (ReachB_symm hix) hiy)

lemma mem_componentsB_iff {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a)) :
    J ∈ componentsB bank ↔ ∃ i : Fin a, J = compOf bank i := by
  constructor
  · intro hJ
    rw [componentsB, Finset.mem_filter] at hJ
    rcases hJ with ⟨_, ⟨i, hi⟩, hJcl, hJmin⟩
    have hsub : compOf bank i ⊆ J := by
      intro y hy
      exact closedB_reach hJcl hi ((mem_compOf bank i y).1 hy)
    have heq := hJmin (compOf bank i) (Finset.mem_powerset.2 hsub)
      ⟨i, self_mem_compOf bank i⟩ (compOf_closedB bank i)
    exact ⟨i, heq.symm⟩
  · rintro ⟨i, rfl⟩
    exact compOf_mem_componentsB bank i

lemma componentsB_disjoint {n a : Nat} (bank : Fin a → Finset (Fin n))
    {J₁ J₂ : Finset (Fin a)} (h1 : J₁ ∈ componentsB bank) (h2 : J₂ ∈ componentsB bank)
    (hne : J₁ ≠ J₂) : Disjoint J₁ J₂ := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases (mem_componentsB_iff bank J₁).1 h1 with ⟨i1, rfl⟩
  rcases (mem_componentsB_iff bank J₂).1 h2 with ⟨i2, rfl⟩
  have hr1 : ReachB bank i1 x := (mem_compOf bank i1 x).1 hx1
  have hr2 : ReachB bank i2 x := (mem_compOf bank i2 x).1 hx2
  exact hne (compOf_eq_of_reach bank (ReachB_trans hr1 (ReachB_symm hr2)))

lemma componentsB_support_disjoint {n a : Nat} (bank : Fin a → Finset (Fin n))
    {J₁ J₂ : Finset (Fin a)} (h1 : J₁ ∈ componentsB bank) (h2 : J₂ ∈ componentsB bank)
    (hne : J₁ ≠ J₂) : Disjoint (supportB bank J₁) (supportB bank J₂) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  rw [supportB, Finset.mem_biUnion] at hv1 hv2
  rcases hv1 with ⟨i1, hi1, hvi1⟩
  rcases hv2 with ⟨i2, hi2, hvi2⟩
  have hcl1 : closedB bank J₁ = true := (Finset.mem_filter.1 h1).2.2.1
  have hi2_in_1 : i2 ∈ J₁ :=
    (closedB_iff bank J₁).1 hcl1 i1 hi1 i2 ⟨v, Finset.mem_inter.2 ⟨hvi1, hvi2⟩⟩
  exact Finset.disjoint_left.1 (componentsB_disjoint bank h1 h2 hne) hi2_in_1 hi2

lemma componentsB_biUnion_id {n a : Nat} (bank : Fin a → Finset (Fin n)) :
    (componentsB bank).biUnion id = Finset.univ := by
  ext i
  simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
  exact ⟨compOf bank i, compOf_mem_componentsB bank i, self_mem_compOf bank i⟩

lemma componentsB_biUnion_support {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hcov : ∀ v : Fin n, ∃ i : Fin a, v ∈ bank i) :
    (componentsB bank).biUnion (supportB bank) = Finset.univ := by
  ext v
  simp only [Finset.mem_biUnion, supportB, Finset.mem_univ, iff_true]
  rcases hcov v with ⟨i, hi⟩
  exact ⟨compOf bank i, compOf_mem_componentsB bank i, i, self_mem_compOf bank i, hi⟩

lemma closedB_disjoint_support {n a : Nat} {bank : Fin a → Finset (Fin n)} {J : Finset (Fin a)}
    (hJ : closedB bank J = true) {i : Fin a} (hi : i ∉ J) :
    Disjoint (supportB bank J) (bank i) := by
  rw [Finset.disjoint_left]
  intro v hv hvi
  rw [supportB, Finset.mem_biUnion] at hv
  rcases hv with ⟨j, hj, hvj⟩
  exact hi ((closedB_iff bank J).1 hJ j hj i ⟨v, Finset.mem_inter.2 ⟨hvj, hvi⟩⟩)

-- Internal connectedness within a subset J of scopes
def AdjIn {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a)) (i h : Fin a) : Prop :=
  i ∈ J ∧ h ∈ J ∧ (bank i ∩ bank h).Nonempty

def ReachIn {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a)) : Fin a → Fin a → Prop :=
  Relation.ReflTransGen (AdjIn bank J)

lemma ReachIn_symm {n a : Nat} {bank : Fin a → Finset (Fin n)} {J : Finset (Fin a)} {i j : Fin a}
    (h : ReachIn bank J i j) : ReachIn bank J j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨ha, hb, hab⟩
    exact Relation.ReflTransGen.head ⟨hb, ha, by simpa [Finset.inter_comm] using hab⟩ ih

lemma ReachIn_mono {n a : Nat} {bank : Fin a → Finset (Fin n)} {J₁ J₂ : Finset (Fin a)}
    (hsub : J₁ ⊆ J₂) {i j : Fin a} (h : ReachIn bank J₁ i j) : ReachIn bank J₂ i j := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨ha, hb, hab⟩
    exact Relation.ReflTransGen.tail ih ⟨hsub ha, hsub hb, hab⟩

def Conn {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a)) : Prop :=
  ∀ i ∈ J, ∀ h ∈ J, ReachIn bank J i h

lemma component_conn {n a : Nat} (bank : Fin a → Finset (Fin n)) {J : Finset (Fin a)}
    (hJ : J ∈ componentsB bank) : Conn bank J := by
  rcases (mem_componentsB_iff bank J).1 hJ with ⟨r, rfl⟩
  have hcl : closedB bank (compOf bank r) = true := compOf_closedB bank r
  intro i hi h hh
  have hr : ReachB bank i h :=
    ReachB_trans (ReachB_symm ((mem_compOf bank r i).1 hi)) ((mem_compOf bank r h).1 hh)
  clear hh
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hbc hstep ih =>
    have hb : b ∈ compOf bank r := closedB_reach hcl hi hbc
    have hc : c ∈ compOf bank r := (closedB_iff bank _).1 hcl b hb c hstep
    exact Relation.ReflTransGen.tail ih ⟨hb, hc, hstep⟩

noncomputable def subCompOf {n a : Nat} (bank : Fin a → Finset (Fin n)) (H : Finset (Fin a)) (i : Fin a) :
    Finset (Fin a) := by
  classical
  exact H.filter (fun h => ReachIn bank H i h)

noncomputable def subComps {n a : Nat} (bank : Fin a → Finset (Fin n)) (H : Finset (Fin a)) :
    Finset (Finset (Fin a)) := by
  classical
  exact H.image (subCompOf bank H)

lemma mem_subCompOf {n a : Nat} (bank : Fin a → Finset (Fin n)) (H : Finset (Fin a)) (i h : Fin a) :
    h ∈ subCompOf bank H i ↔ h ∈ H ∧ ReachIn bank H i h := by
  classical
  simp [subCompOf]

lemma subCompOf_subset {n a : Nat} (bank : Fin a → Finset (Fin n)) (H : Finset (Fin a)) (i : Fin a) :
    subCompOf bank H i ⊆ H := fun _ hx => ((mem_subCompOf bank H i _).1 hx).1

lemma subCompOf_conn {n a : Nat} (bank : Fin a → Finset (Fin n)) (H : Finset (Fin a)) (i : Fin a) :
    Conn bank (subCompOf bank H i) := by
  intro x hx y hy
  rcases (mem_subCompOf bank H i x).1 hx with ⟨hxH, hix⟩
  rcases (mem_subCompOf bank H i y).1 hy with ⟨hyH, hiy⟩
  have hxy : ReachIn bank H x y := Relation.ReflTransGen.trans (ReachIn_symm hix) hiy
  clear hy hyH hiy
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxb hstep ih =>
    have hb : b ∈ subCompOf bank H i :=
      (mem_subCompOf bank H i b).2 ⟨hstep.1, Relation.ReflTransGen.trans hix hxb⟩
    have hc : c ∈ subCompOf bank H i :=
      (mem_subCompOf bank H i c).2 ⟨hstep.2.1,
        Relation.ReflTransGen.tail (Relation.ReflTransGen.trans hix hxb) hstep⟩
    exact Relation.ReflTransGen.tail ih ⟨hb, hc, hstep.2.2⟩

lemma subComps_disjoint {n a : Nat} (bank : Fin a → Finset (Fin n)) (H : Finset (Fin a))
    {C₁ C₂ : Finset (Fin a)} (h1 : C₁ ∈ subComps bank H) (h2 : C₂ ∈ subComps bank H)
    (hne : C₁ ≠ C₂) : Disjoint C₁ C₂ := by
  classical
  simp only [subComps, Finset.mem_image] at h1 h2
  rcases h1 with ⟨i1, _, rfl⟩
  rcases h2 with ⟨i2, _, rfl⟩
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have hr1 := ((mem_subCompOf bank H i1 x).1 hx1).2
  have hr2 := ((mem_subCompOf bank H i2 x).1 hx2).2
  have h12 := Relation.ReflTransGen.trans hr1 (ReachIn_symm hr2)
  apply hne
  ext y
  simp only [mem_subCompOf]
  exact ⟨fun ⟨hy, h⟩ => ⟨hy, Relation.ReflTransGen.trans (ReachIn_symm h12) h⟩,
    fun ⟨hy, h⟩ => ⟨hy, Relation.ReflTransGen.trans h12 h⟩⟩

lemma subComps_support_disjoint {n a : Nat} (bank : Fin a → Finset (Fin n)) (H : Finset (Fin a))
    {C₁ C₂ : Finset (Fin a)} (h1 : C₁ ∈ subComps bank H) (h2 : C₂ ∈ subComps bank H)
    (hne : C₁ ≠ C₂) : Disjoint (supportB bank C₁) (supportB bank C₂) := by
  classical
  have h1' := h1
  simp only [subComps, Finset.mem_image] at h1'
  rcases h1' with ⟨i1, _, hC1⟩
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  rw [supportB, Finset.mem_biUnion] at hv1 hv2
  rcases hv1 with ⟨x1, hx1, hvx1⟩
  rcases hv2 with ⟨x2, hx2, hvx2⟩
  have hx1' : x1 ∈ subCompOf bank H i1 := by rwa [hC1]
  have hx1H : x1 ∈ H := ((mem_subCompOf bank H i1 x1).1 hx1').1
  have hr1 : ReachIn bank H i1 x1 := ((mem_subCompOf bank H i1 x1).1 hx1').2
  have hx2H : x2 ∈ H := by
    simp only [subComps, Finset.mem_image] at h2
    rcases h2 with ⟨i2, _, rfl⟩
    exact ((mem_subCompOf bank H i2 x2).1 hx2).1
  have hx2_in_1 : x2 ∈ C₁ := by
    rw [← hC1, mem_subCompOf]
    exact ⟨hx2H, Relation.ReflTransGen.tail hr1 ⟨hx1H, hx2H, ⟨v, Finset.mem_inter.2 ⟨hvx1, hvx2⟩⟩⟩⟩
  exact Finset.disjoint_left.1 (subComps_disjoint bank H h1 h2 hne) hx2_in_1 hx2

lemma subComps_biUnion_id {n a : Nat} (bank : Fin a → Finset (Fin n)) (H : Finset (Fin a)) :
    (subComps bank H).biUnion id = H := by
  classical
  ext x
  simp only [Finset.mem_biUnion, id_eq, subComps, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨i, _, rfl⟩, hx⟩
    exact ((mem_subCompOf bank H i x).1 hx).1
  · intro hx
    exact ⟨subCompOf bank H x, ⟨x, hx, rfl⟩, (mem_subCompOf bank H x x).2 ⟨hx, Relation.ReflTransGen.refl⟩⟩

-- ============================================================================
-- Section 3: Growing Subset, Edge Lower Bound, Tree Leaf & Orientation
-- ============================================================================

lemma exists_attach {n a : Nat} (bank : Fin a → Finset (Fin n)) {J A : Finset (Fin a)}
    (hconn : Conn bank J) (hAJ : A ⊆ J) (hAne : A.Nonempty) (hdiff : (J \ A).Nonempty) :
    ∃ i ∈ J \ A, (bank i ∩ supportB bank A).Nonempty := by
  rcases hAne with ⟨x, hxA⟩
  rcases hdiff with ⟨y, hy⟩
  have hyJ : y ∈ J := (Finset.mem_sdiff.1 hy).1
  have hyA : y ∉ A := (Finset.mem_sdiff.1 hy).2
  have hxy : ReachIn bank J x y := hconn x (hAJ hxA) y hyJ
  have hex : ∀ {u v : Fin a}, ReachIn bank J u v → u ∈ A → v ∉ A →
      ∃ i ∈ J \ A, (bank i ∩ supportB bank A).Nonempty := by
    intro u v huv
    induction huv with
    | refl => intro hu hv; exact False.elim (hv hu)
    | @tail b c hub hstep ih =>
      intro hu hcA
      by_cases hbA : b ∈ A
      · refine ⟨c, Finset.mem_sdiff.2 ⟨hstep.2.1, hcA⟩, ?_⟩
        rcases hstep.2.2 with ⟨w, hw⟩
        rw [Finset.mem_inter] at hw
        exact ⟨w, Finset.mem_inter.2 ⟨hw.2, Finset.mem_biUnion.2 ⟨b, hbA, hw.1⟩⟩⟩
      · exact ih hu hbA
  exact hex hxy hxA hyA

lemma conn_insert {n a : Nat} (bank : Fin a → Finset (Fin n)) {A : Finset (Fin a)}
    (hconn : Conn bank A) {i : Fin a} (hatt : (bank i ∩ supportB bank A).Nonempty) :
    Conn bank (insert i A) := by
  rcases hatt with ⟨v, hv⟩
  rw [Finset.mem_inter, supportB, Finset.mem_biUnion] at hv
  rcases hv with ⟨hvi, j, hjA, hvj⟩
  have hsub : A ⊆ insert i A := Finset.subset_insert i A
  have hij : ReachIn bank (insert i A) i j :=
    Relation.ReflTransGen.single ⟨Finset.mem_insert_self i A, hsub hjA,
      ⟨v, Finset.mem_inter.2 ⟨hvi, hvj⟩⟩⟩
  have hji : ReachIn bank (insert i A) j i := ReachIn_symm hij
  intro x hx y hy
  rcases Finset.mem_insert.1 hx with rfl | hxA
  · rcases Finset.mem_insert.1 hy with rfl | hyA
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.trans hij (ReachIn_mono hsub (hconn j hjA y hyA))
  · rcases Finset.mem_insert.1 hy with rfl | hyA
    · exact Relation.ReflTransGen.trans (ReachIn_mono hsub (hconn x hxA j hjA)) hji
    · exact ReachIn_mono hsub (hconn x hxA y hyA)

lemma exists_conn_subset_of_card {n a : Nat} (bank : Fin a → Finset (Fin n)) {J : Finset (Fin a)}
    (hconn : Conn bank J) (hJne : J.Nonempty) :
    ∀ m, 1 ≤ m → m ≤ J.card → ∃ A ⊆ J, Conn bank A ∧ A.card = m := by
  intro m hm1 hmJ
  induction m with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      rcases hJne with ⟨i₀, hi₀⟩
      refine ⟨{i₀}, Finset.singleton_subset_iff.2 hi₀, ?_, Finset.card_singleton i₀⟩
      intro x hx y hy
      rw [Finset.mem_singleton] at hx hy
      subst hx; subst hy
      exact Relation.ReflTransGen.refl
    · have hk1 : 1 ≤ k := by omega
      have hkJ : k ≤ J.card := by omega
      rcases ih hk1 hkJ with ⟨A, hAJ, hAconn, hAcard⟩
      have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
      have hdiff : (J \ A).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        have hJA : J ⊆ A := Finset.sdiff_eq_empty_iff_subset.1 h
        have := Finset.card_le_card hJA
        omega
      rcases exists_attach bank hconn hAJ hAne hdiff with ⟨i, hi, hatt⟩
      have hiJ : i ∈ J := (Finset.mem_sdiff.1 hi).1
      have hiA : i ∉ A := (Finset.mem_sdiff.1 hi).2
      refine ⟨insert i A, Finset.insert_subset hiJ hAJ, conn_insert bank hAconn hatt, ?_⟩
      rw [Finset.card_insert_of_notMem hiA, hAcard]

lemma supportB_insert {n a : Nat} (bank : Fin a → Finset (Fin n)) (i : Fin a) (A : Finset (Fin a)) :
    supportB bank (insert i A) = bank i ∪ supportB bank A := by
  simp [supportB]

lemma conn_edge_le {n a : Nat} (bank : Fin a → Finset (Fin n)) {J : Finset (Fin a)}
    (hconn : Conn bank J) (hJne : J.Nonempty) :
    J.card + (supportB bank J).card ≤ J.sum (fun i => (bank i).card) + 1 := by
  have step : ∀ k, ∀ A ⊆ J, A.Nonempty →
      A.card + (supportB bank A).card ≤ A.sum (fun i => (bank i).card) + 1 →
      (J \ A).card = k →
      J.card + (supportB bank J).card ≤ J.sum (fun i => (bank i).card) + 1 := by
    intro k
    induction k with
    | zero =>
      intro A hAJ _ hle hcard
      have hsub : J ⊆ A := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hcard)
      have heq : A = J := Finset.Subset.antisymm hAJ hsub
      simpa [heq] using hle
    | succ m ih =>
      intro A hAJ hAne hle hcard
      have hdiff : (J \ A).Nonempty := Finset.card_pos.1 (by omega)
      rcases exists_attach bank hconn hAJ hAne hdiff with ⟨i, hi, hatt⟩
      have hiJ : i ∈ J := (Finset.mem_sdiff.1 hi).1
      have hiA : i ∉ A := (Finset.mem_sdiff.1 hi).2
      have h1 : 1 ≤ (bank i ∩ supportB bank A).card := Finset.card_pos.2 hatt
      have hcard_u := Finset.card_union_add_card_inter (bank i) (supportB bank A)
      have hle' : (insert i A).card + (supportB bank (insert i A)).card ≤
          (insert i A).sum (fun j => (bank j).card) + 1 := by
        rw [Finset.card_insert_of_notMem hiA, supportB_insert, Finset.sum_insert hiA]
        omega
      have hsdiff : J \ insert i A = (J \ A).erase i := by
        ext x; simp [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
      have hcard' : (J \ insert i A).card = m := by
        rw [hsdiff, Finset.card_erase_of_mem hi, hcard]; omega
      exact ih (insert i A) (Finset.insert_subset hiJ hAJ) (Finset.insert_nonempty i A) hle' hcard'
  rcases hJne with ⟨i₀, hi₀⟩
  refine step (J \ {i₀}).card {i₀} (Finset.singleton_subset_iff.2 hi₀)
    (Finset.singleton_nonempty i₀) ?_ rfl
  simp [supportB]; omega

lemma tree_exists_leaf {n a : Nat} (bank : Fin a → Finset (Fin n)) {J : Finset (Fin a)}
    (hconn : Conn bank J) (hcard : 2 ≤ J.card)
    (htree : J.sum (fun i => (bank i).card) + 1 = J.card + (supportB bank J).card) :
    ∃ i₀ ∈ J, Conn bank (J.erase i₀) ∧ (J.erase i₀).Nonempty ∧
      (∃ v₀, bank i₀ ∩ supportB bank (J.erase i₀) = {v₀}) ∧
      (J.erase i₀).sum (fun i => (bank i).card) + 1 =
        (J.erase i₀).card + (supportB bank (J.erase i₀)).card := by
  have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
  rcases exists_conn_subset_of_card bank hconn hJne (J.card - 1) (by omega) (by omega) with
    ⟨A, hAJ, hAconn, hAcard⟩
  have hdiff_card : (J \ A).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hAJ, hAcard]; omega
  rcases Finset.card_eq_one.1 hdiff_card with ⟨i₀, hi₀eq⟩
  have hi₀mem : i₀ ∈ J \ A := by rw [hi₀eq]; exact Finset.mem_singleton_self i₀
  have hi₀J : i₀ ∈ J := (Finset.mem_sdiff.1 hi₀mem).1
  have hi₀A : i₀ ∉ A := (Finset.mem_sdiff.1 hi₀mem).2
  have hAeq : A = J.erase i₀ := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_erase.2 ⟨fun h => hi₀A (h ▸ hx), hAJ hx⟩
    · intro hx
      rcases Finset.mem_erase.1 hx with ⟨hneq, hxJ⟩
      by_contra hxA
      have : x ∈ J \ A := Finset.mem_sdiff.2 ⟨hxJ, hxA⟩
      rw [hi₀eq, Finset.mem_singleton] at this
      exact hneq this
  subst hAeq
  have hAne : (J.erase i₀).Nonempty := Finset.card_pos.1 (by omega)
  have hatt : (bank i₀ ∩ supportB bank (J.erase i₀)).Nonempty := by
    rcases exists_attach bank hconn (Finset.erase_subset i₀ J) hAne
      ⟨i₀, Finset.mem_sdiff.2 ⟨hi₀J, Finset.notMem_erase i₀ J⟩⟩ with ⟨j, hj, hjb⟩
    have hj' : j = i₀ := by
      have : j ∈ J \ J.erase i₀ := hj
      rw [hi₀eq, Finset.mem_singleton] at this
      exact this
    exact hj' ▸ hjb
  have hAle := conn_edge_le bank hAconn hAne
  have hJins : insert i₀ (J.erase i₀) = J := Finset.insert_erase hi₀J
  have hJsum : J.sum (fun i => (bank i).card) =
      (bank i₀).card + (J.erase i₀).sum (fun i => (bank i).card) := by
    conv_lhs => rw [← hJins]
    rw [Finset.sum_insert (Finset.notMem_erase i₀ J)]
  have hJsupp : supportB bank J = bank i₀ ∪ supportB bank (J.erase i₀) := by
    conv_lhs => rw [← hJins]
    rw [supportB_insert]
  have hu := Finset.card_union_add_card_inter (bank i₀) (supportB bank (J.erase i₀))
  have hinter_pos : 1 ≤ (bank i₀ ∩ supportB bank (J.erase i₀)).card := Finset.card_pos.2 hatt
  have hJcard : J.card = (J.erase i₀).card + 1 := by
    conv_lhs => rw [← hJins]
    rw [Finset.card_insert_of_notMem (Finset.notMem_erase i₀ J)]
  rw [hJsupp] at htree
  have hinter1 : (bank i₀ ∩ supportB bank (J.erase i₀)).card = 1 := by omega
  have hAtree : (J.erase i₀).sum (fun i => (bank i).card) + 1 =
      (J.erase i₀).card + (supportB bank (J.erase i₀)).card := by omega
  exact ⟨i₀, hi₀J, hAconn, hAne, Finset.card_eq_one.1 hinter1, hAtree⟩

lemma grow_orient {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a))
    (hconn : Conn bank J) (hn : Nonempty (Fin n)) :
    ∀ k, ∀ A ⊆ J, A.Nonempty → (J \ A).card = k →
      ∃ π : Fin a → Fin n,
        (∀ i ∈ J \ A, π i ∈ bank i) ∧
        (∀ v ∈ supportB bank J \ supportB bank A, ∃ i ∈ J \ A, v ∈ bank i ∧ π i ≠ v) := by
  classical
  intro k
  induction k with
  | zero =>
    intro A hAJ _ hcard
    have heq : J = A := Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hcard)) hAJ
    refine ⟨fun _ => Classical.arbitrary (Fin n), ?_, ?_⟩
    · intro i hi; rw [heq, Finset.sdiff_self] at hi; exact False.elim (Finset.notMem_empty i hi)
    · intro v hv; rw [heq, Finset.sdiff_self] at hv; exact False.elim (Finset.notMem_empty v hv)
  | succ m ih =>
    intro A hAJ hAne hcard
    have hdiff : (J \ A).Nonempty := Finset.card_pos.1 (by omega)
    rcases exists_attach bank hconn hAJ hAne hdiff with ⟨i, hi, hatt⟩
    have hiJ : i ∈ J := (Finset.mem_sdiff.1 hi).1
    have hiA : i ∉ A := (Finset.mem_sdiff.1 hi).2
    rcases hatt with ⟨u, hu⟩
    rw [Finset.mem_inter] at hu
    have hsdiff : J \ insert i A = (J \ A).erase i := by
      ext x; simp [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    have hcard' : (J \ insert i A).card = m := by
      rw [hsdiff, Finset.card_erase_of_mem hi, hcard]; omega
    rcases ih (insert i A) (Finset.insert_subset hiJ hAJ) (Finset.insert_nonempty i A) hcard' with
      ⟨π', hπ'mem, hπ'cov⟩
    refine ⟨Function.update π' i u, ?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · subst hji; simpa using hu.1
      · rw [Function.update_of_ne hji]
        exact hπ'mem j (by rw [hsdiff]; exact Finset.mem_erase.2 ⟨hji, hj⟩)
    · intro v hv
      rw [Finset.mem_sdiff] at hv
      by_cases hvA' : v ∈ supportB bank (insert i A)
      · rw [supportB_insert, Finset.mem_union] at hvA'
        rcases hvA' with hvi | hvA
        · refine ⟨i, hi, hvi, ?_⟩
          rw [Function.update_self]
          intro huv
          exact hv.2 (huv ▸ hu.2)
        · exact False.elim (hv.2 hvA)
      · rcases hπ'cov v (Finset.mem_sdiff.2 ⟨hv.1, hvA'⟩) with ⟨j, hj, hvj, hneq⟩
        rw [hsdiff] at hj
        rcases Finset.mem_erase.1 hj with ⟨hji, hjJA⟩
        refine ⟨j, hjJA, hvj, ?_⟩
        rwa [Function.update_of_ne hji]

lemma orient_from_root {n a : Nat} (bank : Fin a → Finset (Fin n)) {J : Finset (Fin a)}
    (hconn : Conn bank J) (hn : Nonempty (Fin n)) {i₀ : Fin a} (hi₀ : i₀ ∈ J) :
    ∃ π : Fin a → Fin n,
      (∀ i ∈ J.erase i₀, π i ∈ bank i) ∧
      (∀ v ∈ supportB bank J \ bank i₀, ∃ i ∈ J.erase i₀, v ∈ bank i ∧ π i ≠ v) := by
  rcases grow_orient bank J hconn hn (J \ {i₀}).card {i₀} (Finset.singleton_subset_iff.2 hi₀)
    (Finset.singleton_nonempty i₀) rfl with ⟨π, hmem, hcov⟩
  have heq : J \ {i₀} = J.erase i₀ := by ext x; simp [Finset.mem_sdiff, Finset.mem_erase, and_comm]
  have hsup : supportB bank {i₀} = bank i₀ := by simp [supportB]
  rw [heq] at hmem hcov
  rw [hsup] at hcov
  exact ⟨π, hmem, hcov⟩

lemma nontree_orient {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) (hn : Nonempty (Fin n)) :
    ∀ k, ∀ H : Finset (Fin a), H.card = k → Conn bank H → H.Nonempty →
      H.card + (supportB bank H).card ≤ H.sum (fun i => (bank i).card) →
      ∃ π : Fin a → Fin n,
        (∀ i ∈ H, π i ∈ bank i) ∧
        (∀ v ∈ supportB bank H, ∃ i ∈ H, v ∈ bank i ∧ π i ≠ v) := by
  classical
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro H hHcard hHconn hHne hnt
    rcases hHne with ⟨i₀, hi₀H⟩
    have hH2 : 2 ≤ H.card := by
      by_contra hlt
      have h1 : H.card = 1 := by
        have := Finset.card_pos.2 ⟨i₀, hi₀H⟩; omega
      rcases Finset.card_eq_one.1 h1 with ⟨j, rfl⟩
      simp [supportB] at hnt
    let H' := H.erase i₀
    let Cs := subComps bank H'
    by_cases hex : ∃ C ∈ Cs, C.card + (supportB bank C).card ≤ C.sum (fun i => (bank i).card)
    · rcases hex with ⟨C, hCmem, hCnt⟩
      have hCsub' : C ⊆ H' := by
        simp only [Cs, subComps, Finset.mem_image] at hCmem
        rcases hCmem with ⟨r, _, rfl⟩
        exact subCompOf_subset bank H' r
      have hCsub : C ⊆ H := hCsub'.trans (Finset.erase_subset i₀ H)
      have hCne : C.Nonempty := by
        simp only [Cs, subComps, Finset.mem_image] at hCmem
        rcases hCmem with ⟨r, hr, rfl⟩
        exact ⟨r, (mem_subCompOf bank H' r r).2 ⟨hr, Relation.ReflTransGen.refl⟩⟩
      have hCconn : Conn bank C := by
        simp only [Cs, subComps, Finset.mem_image] at hCmem
        rcases hCmem with ⟨r, _, rfl⟩
        exact subCompOf_conn bank H' r
      have hClt : C.card < k := by
        have hle : C.card ≤ (H.erase i₀).card := Finset.card_le_card hCsub'
        have her := Finset.card_erase_lt_of_mem hi₀H
        omega
      rcases ih C.card hClt C rfl hCconn hCne hCnt with ⟨π₀, hπ₀mem, hπ₀cov⟩
      rcases grow_orient bank H hHconn hn (H \ C).card C hCsub hCne rfl with ⟨π₁, hπ₁mem, hπ₁cov⟩
      refine ⟨fun i => if i ∈ C then π₀ i else π₁ i, ?_, ?_⟩
      · intro i hi
        by_cases hiC : i ∈ C
        · simp [hiC, hπ₀mem i hiC]
        · simp [hiC, hπ₁mem i (Finset.mem_sdiff.2 ⟨hi, hiC⟩)]
      · intro v hv
        by_cases hvC : v ∈ supportB bank C
        · rcases hπ₀cov v hvC with ⟨i, hiC, hvi, hne'⟩
          exact ⟨i, hCsub hiC, hvi, by simp [hiC, hne']⟩
        · rcases hπ₁cov v (Finset.mem_sdiff.2 ⟨hv, hvC⟩) with ⟨i, hiHC, hvi, hne'⟩
          have hiC : i ∉ C := (Finset.mem_sdiff.1 hiHC).2
          exact ⟨i, (Finset.mem_sdiff.1 hiHC).1, hvi, by simp [hiC, hne']⟩
    · push_neg at hex
      -- Every component C of H' is a tree, and meets bank i₀
      have hCtree : ∀ C ∈ Cs, C.sum (fun i => (bank i).card) + 1 =
          C.card + (supportB bank C).card := by
        intro C hCmem
        have hCne : C.Nonempty := by
          simp only [Cs, subComps, Finset.mem_image] at hCmem
          rcases hCmem with ⟨r, hr, rfl⟩
          exact ⟨r, (mem_subCompOf bank H' r r).2 ⟨hr, Relation.ReflTransGen.refl⟩⟩
        have hCconn : Conn bank C := by
          simp only [Cs, subComps, Finset.mem_image] at hCmem
          rcases hCmem with ⟨r, _, rfl⟩
          exact subCompOf_conn bank H' r
        have hle := conn_edge_le bank hCconn hCne
        have hlt := hex C hCmem
        omega
      -- Partition identities for H' = Cs.biUnion id
      have hH'eq : Cs.biUnion id = H' := subComps_biUnion_id bank H'
      have hdisj : Set.PairwiseDisjoint (Cs : Set (Finset (Fin a))) id := fun C1 h1 C2 h2 hne' =>
        subComps_disjoint bank H' h1 h2 hne'
      have hdisjS : Set.PairwiseDisjoint (Cs : Set (Finset (Fin a))) (supportB bank) :=
        fun C1 h1 C2 h2 hne' => subComps_support_disjoint bank H' h1 h2 hne'
      have hH'card : H'.card = Cs.sum Finset.card := by
        rw [← hH'eq, Finset.card_biUnion hdisj]; rfl
      have hH'sum : H'.sum (fun i => (bank i).card) =
          Cs.sum (fun C => C.sum (fun i => (bank i).card)) := by
        rw [← hH'eq, Finset.sum_biUnion hdisj]; rfl
      have hH'supp : supportB bank H' = Cs.biUnion (supportB bank) := by
        rw [← hH'eq]
        ext v
        simp only [supportB, Finset.mem_biUnion, id_eq]
        exact ⟨fun ⟨i, ⟨C, hC, hi⟩, hv⟩ => ⟨C, hC, i, hi, hv⟩,
          fun ⟨C, hC, i, hi, hv⟩ => ⟨i, ⟨C, hC, hi⟩, hv⟩⟩
      have hH'suppCard : (supportB bank H').card = Cs.sum (fun C => (supportB bank C).card) := by
        rw [hH'supp, Finset.card_biUnion hdisjS]
      have hinter_eq : bank i₀ ∩ supportB bank H' = Cs.biUnion (fun C => bank i₀ ∩ supportB bank C) := by
        rw [hH'supp]
        ext v
        simp only [Finset.mem_inter, Finset.mem_biUnion]
        exact ⟨fun ⟨h1, C, hC, h2⟩ => ⟨C, hC, h1, h2⟩,
          fun ⟨C, hC, h1, h2⟩ => ⟨h1, C, hC, h2⟩⟩
      have hdisjI : Set.PairwiseDisjoint (Cs : Set (Finset (Fin a)))
          (fun C => bank i₀ ∩ supportB bank C) := by
        intro C1 h1 C2 h2 hne'
        exact (hdisjS h1 h2 hne').mono Finset.inter_subset_right Finset.inter_subset_right
      have hinterCard : (bank i₀ ∩ supportB bank H').card =
          Cs.sum (fun C => (bank i₀ ∩ supportB bank C).card) := by
        rw [hinter_eq, Finset.card_biUnion hdisjI]
      have hHins : insert i₀ H' = H := Finset.insert_erase hi₀H
      have hHcard' : H.card = H'.card + 1 := by
        rw [← hHins, Finset.card_insert_of_notMem (Finset.notMem_erase i₀ H)]
      have hHsum' : H.sum (fun i => (bank i).card) =
          (bank i₀).card + H'.sum (fun i => (bank i).card) := by
        rw [← hHins, Finset.sum_insert (Finset.notMem_erase i₀ H)]
      have hHsupp' : supportB bank H = bank i₀ ∪ supportB bank H' := by
        rw [← hHins, supportB_insert]
      have hu := Finset.card_union_add_card_inter (bank i₀) (supportB bank H')
      have hsum_tree : Cs.sum (fun C => C.sum (fun i => (bank i).card)) + Cs.card =
          Cs.sum Finset.card + Cs.sum (fun C => (supportB bank C).card) := by
        have h1 : Cs.sum (fun C => C.sum (fun i => (bank i).card) + 1) =
            Cs.sum (fun C => C.card + (supportB bank C).card) :=
          Finset.sum_congr rfl hCtree
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h1
        exact h1
      have hsum_gt : Cs.card < Cs.sum (fun C => (bank i₀ ∩ supportB bank C).card) := by
        rw [hHsupp'] at hnt
        omega
      -- By pigeonhole, some C ∈ Cs has ≥ 2 vertices in bank i₀ ∩ supportB bank C
      have hex2 : ∃ C ∈ Cs, 2 ≤ (bank i₀ ∩ supportB bank C).card := by
        by_contra hall
        push_neg at hall
        have hle : Cs.sum (fun C => (bank i₀ ∩ supportB bank C).card) ≤ Cs.sum (fun _ => 1) := by
          apply Finset.sum_le_sum
          intro C hC; have := hall C hC; omega
        simp at hle
        omega
      rcases hex2 with ⟨C, hCmem, hC2⟩
      have hCsub' : C ⊆ H' := by
        simp only [Cs, subComps, Finset.mem_image] at hCmem
        rcases hCmem with ⟨r, _, rfl⟩
        exact subCompOf_subset bank H' r
      have hCsub : C ⊆ H := hCsub'.trans (Finset.erase_subset i₀ H)
      have hi₀C : i₀ ∉ C := fun h => (Finset.notMem_erase i₀ H) (hCsub' h)
      have hCconn : Conn bank C := by
        simp only [Cs, subComps, Finset.mem_image] at hCmem
        rcases hCmem with ⟨r, _, rfl⟩
        exact subCompOf_conn bank H' r
      rcases Finset.one_lt_card.1 (by omega : 1 < (bank i₀ ∩ supportB bank C).card) with
        ⟨v₁, hv₁, v₂, hv₂, hv12⟩
      rw [Finset.mem_inter] at hv₁ hv₂
      have hv1C : v₁ ∈ supportB bank C := hv₁.2
      rw [supportB, Finset.mem_biUnion] at hv1C
      rcases hv1C with ⟨j₀, hj₀C, hv1j₀⟩
      have hj₀ne : j₀ ≠ i₀ := fun h => hi₀C (h ▸ hj₀C)
      rcases orient_from_root bank hCconn hn hj₀C with ⟨πC, hπCmem, hπCcov⟩
      let A := insert i₀ C
      have hAH : A ⊆ H := Finset.insert_subset hi₀H hCsub
      have hAne : A.Nonempty := Finset.insert_nonempty i₀ C
      let π₀ : Fin a → Fin n := fun i =>
        if i = i₀ then v₂ else if i = j₀ then v₁ else πC i
      have hπ₀mem : ∀ i ∈ A, π₀ i ∈ bank i := by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hiC
        · simp [π₀, hv₂.1]
        · have hii₀ : i ≠ i₀ := fun h => hi₀C (h ▸ hiC)
          by_cases hij₀ : i = j₀
          · subst hij₀; simp [π₀, hii₀, hv1j₀]
          · simp [π₀, hii₀, hij₀, hπCmem i (Finset.mem_erase.2 ⟨hij₀, hiC⟩)]
      have hπ₀cov : ∀ v ∈ supportB bank A, ∃ i ∈ A, v ∈ bank i ∧ π₀ i ≠ v := by
        intro v hv
        rw [supportB_insert, Finset.mem_union] at hv
        by_cases hvi₀ : v ∈ bank i₀ ∧ v ≠ v₂
        · exact ⟨i₀, Finset.mem_insert_self i₀ C, hvi₀.1, by simp [π₀, hvi₀.2.symm]⟩
        · have hvC : v ∈ supportB bank C := by
            rcases hv with h1 | h2
            · have hv2eq : v = v₂ := by tauto
              subst hv2eq; exact hv₂.2
            · exact h2
          by_cases hvj₀ : v ∈ bank j₀
          · have hvne1 : v ≠ v₁ := by
              intro h
              subst h
              exact hvi₀ ⟨hv₁.1, hv12⟩
            exact ⟨j₀, Finset.mem_insert_of_mem hj₀C, hvj₀, by simp [π₀, hj₀ne, hvne1.symm]⟩
          · rcases hπCcov v (Finset.mem_sdiff.2 ⟨hvC, hvj₀⟩) with ⟨i, hi, hvi, hne'⟩
            rcases Finset.mem_erase.1 hi with ⟨hij₀, hiC⟩
            have hii₀ : i ≠ i₀ := fun h => hi₀C (h ▸ hiC)
            exact ⟨i, Finset.mem_insert_of_mem hiC, hvi, by simp [π₀, hii₀, hij₀, hne']⟩
      rcases grow_orient bank H hHconn hn (H \ A).card A hAH hAne rfl with ⟨π₁, hπ₁mem, hπ₁cov⟩
      refine ⟨fun i => if i ∈ A then π₀ i else π₁ i, ?_, ?_⟩
      · intro i hi
        by_cases hiA : i ∈ A
        · simp [hiA, hπ₀mem i hiA]
        · simp [hiA, hπ₁mem i (Finset.mem_sdiff.2 ⟨hi, hiA⟩)]
      · intro v hv
        by_cases hvA : v ∈ supportB bank A
        · rcases hπ₀cov v hvA with ⟨i, hiA, hvi, hne'⟩
          exact ⟨i, hAH hiA, hvi, by simp [hiA, hne']⟩
        · rcases hπ₁cov v (Finset.mem_sdiff.2 ⟨hv, hvA⟩) with ⟨i, hiHA, hvi, hne'⟩
          have hiA : i ∉ A := (Finset.mem_sdiff.1 hiHA).2
          exact ⟨i, (Finset.mem_sdiff.1 hiHA).1, hvi, by simp [hiA, hne']⟩

-- ============================================================================
-- Section 4: Linear Span Algebra (PatOn, InSpan) and Mersenne Bezout
-- ============================================================================

def PatOn {n a : Nat} (bank : Fin a → Finset (Fin n)) (S : Finset (Fin a)) :
    Finset (Fin a → Finset (Fin n)) :=
  (Finset.univ : Finset (Fin a → Finset (Fin n))).filter
    (fun p => (∀ i ∈ S, p i ⊆ bank i) ∧ (∀ i ∉ S, p i = ∅))

def InSpan {n a : Nat} (bank : Fin a → Finset (Fin n)) (S : Finset (Fin a))
    (f : Finset (Fin n) → Int) : Prop :=
  ∃ c : (Fin a → Finset (Fin n)) → Int, ∀ x : Finset (Fin n),
    ((PatOn bank S).filter (fun p => ∀ i ∈ S, x ∩ bank i ≠ p i)).sum c = f x

lemma InSpan_univ_imp_canRecover {n a : Nat} (bank : Fin a → Finset (Fin n))
    (h : ∀ z : Finset (Fin n), InSpan bank Finset.univ (fun x => if x = z then 1 else 0)) :
    canRecoverB a bank := by
  intro z
  rcases h z with ⟨c, hc⟩
  refine ⟨c, fun x => ?_⟩
  have hpat : PatOn bank Finset.univ =
      (Finset.univ : Finset (Fin a → Finset (Fin n))).filter (fun p => ∀ i, p i ⊆ bank i) := by
    ext p; simp [PatOn]
  have hfilt : (PatOn bank Finset.univ).filter (fun p => ∀ i ∈ (Finset.univ : Finset (Fin a)), x ∩ bank i ≠ p i) =
      ((Finset.univ : Finset (Fin a → Finset (Fin n))).filter (fun p => ∀ i, p i ⊆ bank i)).filter
        (fun p => ∀ i, x ∩ bank i ≠ p i) := by
    rw [hpat]; ext p; simp
  rw [← hfilt]
  exact hc x

lemma InSpan_zero {n a : Nat} (bank : Fin a → Finset (Fin n)) (S : Finset (Fin a)) :
    InSpan bank S (fun _ => 0) :=
  ⟨fun _ => 0, fun _ => by simp⟩

lemma InSpan_add {n a : Nat} {bank : Fin a → Finset (Fin n)} {S : Finset (Fin a)}
    {f g : Finset (Fin n) → Int} (hf : InSpan bank S f) (hg : InSpan bank S g) :
    InSpan bank S (fun x => f x + g x) := by
  rcases hf with ⟨cf, hcf⟩
  rcases hg with ⟨cg, hcg⟩
  refine ⟨fun p => cf p + cg p, fun x => ?_⟩
  rw [Finset.sum_add_distrib, hcf x, hcg x]

lemma InSpan_smul {n a : Nat} {bank : Fin a → Finset (Fin n)} {S : Finset (Fin a)}
    (m : Int) {f : Finset (Fin n) → Int} (hf : InSpan bank S f) :
    InSpan bank S (fun x => m * f x) := by
  rcases hf with ⟨c, hc⟩
  refine ⟨fun p => m * c p, fun x => ?_⟩
  rw [← Finset.mul_sum, hc x]

lemma InSpan_sum {n a : Nat} {ι : Type*} [DecidableEq ι] (bank : Fin a → Finset (Fin n))
    (S : Finset (Fin a)) (I : Finset ι) (f : ι → Finset (Fin n) → Int)
    (hf : ∀ j ∈ I, InSpan bank S (f j)) :
    InSpan bank S (fun x => I.sum (fun j => f j x)) := by
  induction I using Finset.induction_on with
  | empty =>
    simpa using InSpan_zero bank S
  | @insert j I hj ih =>
    have h1 := hf j (Finset.mem_insert_self j I)
    have h2 := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    have := InSpan_add h1 h2
    simpa [Finset.sum_insert hj] using this

lemma InSpan_empty_one {n a : Nat} (bank : Fin a → Finset (Fin n)) :
    InSpan bank ∅ (fun _ => 1) := by
  refine ⟨fun _ => 1, fun x => ?_⟩
  have heq : (PatOn bank ∅).filter (fun p => ∀ i ∈ (∅ : Finset (Fin a)), x ∩ bank i ≠ p i) =
      {fun _ => ∅} := by
    ext p
    simp only [Finset.mem_filter, PatOn, Finset.mem_univ, true_and, Finset.notMem_empty,
      not_false_eq_true, true_implies, false_implies, implies_true, and_true, Finset.mem_singleton]
    exact ⟨fun h => funext h, fun h i => by rw [h]⟩
  rw [heq]; simp

lemma InSpan_mul_disjoint {n a : Nat} {bank : Fin a → Finset (Fin n)}
    {S₁ S₂ : Finset (Fin a)} (hdisj : Disjoint S₁ S₂)
    {f₁ f₂ : Finset (Fin n) → Int} (h1 : InSpan bank S₁ f₁) (h2 : InSpan bank S₂ f₂) :
    InSpan bank (S₁ ∪ S₂) (fun x => f₁ x * f₂ x) := by
  classical
  rcases h1 with ⟨c₁, hc₁⟩
  rcases h2 with ⟨c₂, hc₂⟩
  let r₁ : (Fin a → Finset (Fin n)) → (Fin a → Finset (Fin n)) :=
    fun p i => if i ∈ S₁ then p i else ∅
  let r₂ : (Fin a → Finset (Fin n)) → (Fin a → Finset (Fin n)) :=
    fun p i => if i ∈ S₂ then p i else ∅
  refine ⟨fun p => c₁ (r₁ p) * c₂ (r₂ p), fun x => ?_⟩
  let A₁ := (PatOn bank S₁).filter (fun p => ∀ i ∈ S₁, x ∩ bank i ≠ p i)
  let A₂ := (PatOn bank S₂).filter (fun p => ∀ i ∈ S₂, x ∩ bank i ≠ p i)
  let A₁₂ := (PatOn bank (S₁ ∪ S₂)).filter (fun p => ∀ i ∈ S₁ ∪ S₂, x ∩ bank i ≠ p i)
  have hprod : A₁.sum c₁ * A₂.sum c₂ = (A₁ ×ˢ A₂).sum (fun pq => c₁ pq.1 * c₂ pq.2) := by
    rw [Finset.sum_product, Finset.sum_mul]
    congr 1; ext p₁; rw [Finset.mul_sum]
  dsimp only
  rw [← hc₁ x, ← hc₂ x]
  change A₁₂.sum (fun p => c₁ (r₁ p) * c₂ (r₂ p)) = A₁.sum c₁ * A₂.sum c₂
  rw [hprod]
  symm
  refine Finset.sum_bij (fun pq _ => fun i => if i ∈ S₁ then pq.1 i else pq.2 i) ?_ ?_ ?_ ?_
  · rintro ⟨p₁, p₂⟩ hpq
    rw [Finset.mem_product] at hpq
    rcases hpq with ⟨hp₁, hp₂⟩
    simp only [A₁, A₂, A₁₂, PatOn, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂ ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi
      rcases Finset.mem_union.1 hi with hi1 | hi2
      · simp [hi1, hp₁.1.1 i hi1]
      · have hi1 : i ∉ S₁ := Finset.disjoint_right.1 hdisj hi2
        simp [hi1, hp₂.1.1 i hi2]
    · intro i hi
      have hi1 : i ∉ S₁ := fun h => hi (Finset.mem_union_left S₂ h)
      have hi2 : i ∉ S₂ := fun h => hi (Finset.mem_union_right S₁ h)
      simp [hi1, hp₂.1.2 i hi2]
    · intro i hi
      rcases Finset.mem_union.1 hi with hi1 | hi2
      · simp [hi1, hp₁.2 i hi1]
      · have hi1 : i ∉ S₁ := Finset.disjoint_right.1 hdisj hi2
        simp [hi1, hp₂.2 i hi2]
  · rintro ⟨p₁, p₂⟩ hpq ⟨q₁, q₂⟩ hqq heq
    rw [Finset.mem_product] at hpq hqq
    simp only [A₁, A₂, PatOn, Finset.mem_filter, Finset.mem_univ, true_and] at hpq hqq
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · dsimp only
      by_cases hi1 : i ∈ S₁
      · have := congrFun heq i; simpa [hi1] using this
      · rw [hpq.1.1.2 i hi1, hqq.1.1.2 i hi1]
    · dsimp only
      by_cases hi2 : i ∈ S₂
      · have hi1 : i ∉ S₁ := Finset.disjoint_right.1 hdisj hi2
        have := congrFun heq i; simpa [hi1] using this
      · rw [hpq.2.1.2 i hi2, hqq.2.1.2 i hi2]
  · intro p hp
    simp only [A₁₂, PatOn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨(r₁ p, r₂ p), ?_, ?_⟩
    · rw [Finset.mem_product]
      simp only [A₁, A₂, PatOn, Finset.mem_filter, Finset.mem_univ, true_and, r₁, r₂]
      refine ⟨⟨⟨fun i hi => by simp [hi, hp.1.1 i (Finset.mem_union_left S₂ hi)],
        fun i hi => by simp [hi]⟩,
        fun i hi => by simp [hi, hp.2 i (Finset.mem_union_left S₂ hi)]⟩,
        ⟨⟨fun i hi => by simp [hi, hp.1.1 i (Finset.mem_union_right S₁ hi)],
        fun i hi => by simp [hi]⟩,
        fun i hi => by simp [hi, hp.2 i (Finset.mem_union_right S₁ hi)]⟩⟩
    · ext i
      by_cases hi1 : i ∈ S₁
      · simp [r₁, hi1]
      · by_cases hi2 : i ∈ S₂
        · simp [r₂, hi1, hi2]
        · have hi12 : i ∉ S₁ ∪ S₂ := fun h => by rcases Finset.mem_union.1 h with h1 | h2 <;> tauto
          simp [r₂, hi1, hi2, hp.1.2 i hi12]
  · rintro ⟨p₁, p₂⟩ hpq
    rw [Finset.mem_product] at hpq
    simp only [A₁, A₂, PatOn, Finset.mem_filter, Finset.mem_univ, true_and] at hpq
    have h1 : r₁ (fun i => if i ∈ S₁ then p₁ i else p₂ i) = p₁ := by
      ext i
      by_cases hi1 : i ∈ S₁
      · simp [r₁, hi1]
      · simp [r₁, hi1, hpq.1.1.2 i hi1]
    have h2 : r₂ (fun i => if i ∈ S₁ then p₁ i else p₂ i) = p₂ := by
      ext i
      by_cases hi2 : i ∈ S₂
      · have hi1 : i ∉ S₁ := Finset.disjoint_right.1 hdisj hi2
        simp [r₂, hi1, hi2]
      · simp [r₂, hi2, hpq.2.1.2 i hi2]
    rw [h1, h2]

lemma InSpan_prod {n a : Nat} (bank : Fin a → Finset (Fin n)) (S : Finset (Fin a))
    (f : Fin a → Finset (Fin n) → Int) (hf : ∀ i ∈ S, InSpan bank {i} (f i)) :
    InSpan bank S (fun x => S.prod (fun i => f i x)) := by
  induction S using Finset.induction_on with
  | empty =>
    simpa using InSpan_empty_one bank
  | @insert i S hi ih =>
    have h1 := hf i (Finset.mem_insert_self i S)
    have h2 := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hdisj : Disjoint {i} S := Finset.disjoint_singleton_left.2 hi
    have hmul := InSpan_mul_disjoint hdisj h1 h2
    have hunion : ({i} : Finset (Fin a)) ∪ S = insert i S := Finset.singleton_union i S
    rw [hunion] at hmul
    simpa [Finset.prod_insert hi] using hmul

lemma InSpan_biUnion {n a : Nat} (bank : Fin a → Finset (Fin n))
    (Cs : Finset (Finset (Fin a)))
    (hdisj : Set.PairwiseDisjoint (Cs : Set (Finset (Fin a))) id)
    (g : Finset (Fin a) → Finset (Fin n) → Int)
    (hg : ∀ J ∈ Cs, InSpan bank J (g J)) :
    InSpan bank (Cs.biUnion id) (fun x => Cs.prod (fun J => g J x)) := by
  classical
  induction Cs using Finset.induction_on with
  | empty =>
    simpa using InSpan_empty_one bank
  | @insert J Cs hJ ih =>
    have hdisj' : Set.PairwiseDisjoint (Cs : Set (Finset (Fin a))) id :=
      hdisj.subset (Finset.subset_insert J Cs)
    have h1 := hg J (Finset.mem_insert_self J Cs)
    have h2 := ih hdisj' (fun K hK => hg K (Finset.mem_insert_of_mem hK))
    have hd : Disjoint J (Cs.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro K hK
      exact hdisj (Finset.mem_insert_self J Cs) (Finset.mem_insert_of_mem hK)
        (fun h => hJ (h ▸ hK))
    have hmul := InSpan_mul_disjoint hd h1 h2
    have hbu : (insert J Cs).biUnion id = J ∪ Cs.biUnion id := by simp
    rw [hbu]
    simpa [Finset.prod_insert hJ] using hmul

def singlePat {n a : Nat} (i : Fin a) (q : Finset (Fin n)) : Fin a → Finset (Fin n) :=
  fun j => if j = i then q else ∅

lemma singlePat_injective {n a : Nat} (i : Fin a) :
    Function.Injective (singlePat (n := n) i) := by
  intro q1 q2 h
  have := congrFun h i
  simpa [singlePat] using this

lemma PatOn_singleton {n a : Nat} (bank : Fin a → Finset (Fin n)) (i : Fin a) :
    PatOn bank {i} = (bank i).powerset.image (singlePat i) := by
  ext p
  simp only [PatOn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    forall_eq, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hzero⟩
    refine ⟨p i, hsub, ?_⟩
    ext j
    by_cases hji : j = i
    · subst hji; simp [singlePat]
    · simp [singlePat, hji, hzero j hji]
  · rintro ⟨q, hq, rfl⟩
    exact ⟨by simpa [singlePat] using hq, fun j hj => by simp [singlePat, hj]⟩

lemma InSpan_singleton_diff {n a : Nat} (bank : Fin a → Finset (Fin n)) (i : Fin a)
    {q₁ q₂ : Finset (Fin n)} (h1 : q₁ ⊆ bank i) (h2 : q₂ ⊆ bank i) :
    InSpan bank {i} (fun x =>
      (if x ∩ bank i = q₁ then (1 : Int) else 0) - (if x ∩ bank i = q₂ then (1 : Int) else 0)) := by
  classical
  by_cases hq : q₁ = q₂
  · subst hq
    simpa using InSpan_zero bank {i}
  · refine ⟨fun p => (if p = singlePat i q₂ then 1 else 0) - (if p = singlePat i q₁ then 1 else 0),
      fun x => ?_⟩
    rw [PatOn_singleton]
    have hfilt : (((bank i).powerset.image (singlePat i)).filter
        (fun p => ∀ j ∈ ({i} : Finset (Fin a)), x ∩ bank j ≠ p j)) =
        ((bank i).powerset.filter (fun q => x ∩ bank i ≠ q)).image (singlePat i) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton, forall_eq]
      constructor
      · rintro ⟨⟨q, hqP, rfl⟩, hne⟩
        exact ⟨q, ⟨hqP, by simpa [singlePat] using hne⟩, rfl⟩
      · rintro ⟨q, ⟨hqP, hne⟩, rfl⟩
        exact ⟨⟨q, hqP, rfl⟩, by simpa [singlePat] using hne⟩
    rw [hfilt, Finset.sum_image (fun a _ b _ h => singlePat_injective i h)]
    rw [Finset.sum_sub_distrib]
    have hs : ∀ q, q ⊆ bank i →
        ((bank i).powerset.filter (fun r => x ∩ bank i ≠ r)).sum
          (fun r => if singlePat i r = singlePat i q then (1 : Int) else 0) =
          if x ∩ bank i ≠ q then 1 else 0 := by
      intro q hqsub
      have hcongr : ∀ r ∈ (bank i).powerset.filter (fun r => x ∩ bank i ≠ r),
          (if singlePat i r = singlePat i q then (1 : Int) else 0) = if r = q then 1 else 0 := by
        intro r _
        simp [(singlePat_injective i).eq_iff]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
      simp [Finset.mem_filter, Finset.mem_powerset, hqsub]
    rw [hs q₂ h2, hs q₁ h1]
    dsimp only
    by_cases hx1 : x ∩ bank i = q₁ <;> by_cases hx2 : x ∩ bank i = q₂
    · exact False.elim (hq (hx1.symm.trans hx2))
    · simp [hx1, hx2, hq, Ne.symm hq]
    · simp [hx1, hx2, hq, Ne.symm hq]
    · simp [hx1, hx2, hq, Ne.symm hq]

lemma InSpan_singleton_mersenne {n a : Nat} (bank : Fin a → Finset (Fin n)) (i : Fin a)
    {q : Finset (Fin n)} (hq : q ⊆ bank i) :
    InSpan bank {i} (fun x =>
      if x ∩ bank i = q then ((2 ^ (bank i).card - 1 : Nat) : Int) else 0) := by
  classical
  let M : Int := ((2 ^ (bank i).card - 1 : Nat) : Int)
  refine ⟨fun p => 1 - (if p = singlePat i q then M else 0), fun x => ?_⟩
  rw [PatOn_singleton]
  have hfilt : (((bank i).powerset.image (singlePat i)).filter
      (fun p => ∀ j ∈ ({i} : Finset (Fin a)), x ∩ bank j ≠ p j)) =
      ((bank i).powerset.erase (x ∩ bank i)).image (singlePat i) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton, forall_eq,
      Finset.mem_erase]
    constructor
    · rintro ⟨⟨r, hrP, rfl⟩, hne⟩
      exact ⟨r, ⟨by simpa [singlePat, eq_comm] using hne, hrP⟩, rfl⟩
    · rintro ⟨r, ⟨hne, hrP⟩, rfl⟩
      exact ⟨⟨r, hrP, rfl⟩, by simpa [singlePat, eq_comm] using hne⟩
  rw [hfilt, Finset.sum_image (fun a _ b _ h => singlePat_injective i h)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hxmem : x ∩ bank i ∈ (bank i).powerset := Finset.mem_powerset.2 Finset.inter_subset_right
  have hcard : (((bank i).powerset.erase (x ∩ bank i)).card : Int) = M := by
    rw [Finset.card_erase_of_mem hxmem, Finset.card_powerset]
  rw [hcard]
  have hcongr : ∀ r ∈ (bank i).powerset.erase (x ∩ bank i),
      (if singlePat i r = singlePat i q then M else 0) = if r = q then M else 0 := by
    intro r _
    simp [(singlePat_injective i).eq_iff]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
  simp only [Finset.mem_erase, Finset.mem_powerset, hq, and_true]
  by_cases hxq : x ∩ bank i = q
  · simp [hxq, M]
  · have hqx : q ≠ x ∩ bank i := Ne.symm hxq
    simp [hxq, hqx, M]

-- Elementary Mersenne GCD & Finset Bezout
lemma two_pow_sub_one_dvd_mul (v q : Nat) : (2 ^ v - 1) ∣ (2 ^ (q * v) - 1) := by
  induction q with
  | zero => simp
  | succ k ih =>
    rcases ih with ⟨m, hm⟩
    have h1 : 1 ≤ 2 ^ (k * v) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ v := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ (k * v) * 2 ^ v := by nlinarith
    refine ⟨2 ^ v * m + 1, ?_⟩
    have hexp : (k + 1) * v = k * v + v := by ring
    rw [hexp, pow_add]
    zify [h1, h2, h3] at hm ⊢
    nlinarith

lemma gcd_two_pow_sub_one (u v : Nat) :
    Nat.gcd (2 ^ u - 1) (2 ^ v - 1) = 2 ^ (Nat.gcd u v) - 1 := by
  induction u, v using Nat.gcd.induction with
  | H0 v => simp
  | H1 u v hu ih =>
    have hdiv : (2 ^ u - 1) ∣ (2 ^ ((v / u) * u) - 1) := two_pow_sub_one_dvd_mul u (v / u)
    rcases hdiv with ⟨m, hm⟩
    have hvu : v = (v / u) * u + v % u := by
      have := Nat.div_add_mod v u; linarith
    have heq : 2 ^ v - 1 = (2 ^ (v % u) - 1) + (2 ^ u - 1) * (2 ^ (v % u) * m) := by
      have h1 : 1 ≤ 2 ^ ((v / u) * u) := Nat.one_le_two_pow
      have h2 : 1 ≤ 2 ^ (v % u) := Nat.one_le_two_pow
      have h3 : 1 ≤ 2 ^ u := Nat.one_le_two_pow
      have h4 : 1 ≤ 2 ^ v := Nat.one_le_two_pow
      have hp : 2 ^ v = 2 ^ ((v / u) * u) * 2 ^ (v % u) := by
        rw [← pow_add, ← hvu]
      zify [h1, h2, h3, h4] at hm hp ⊢
      nlinarith
    rw [heq, Nat.gcd_add_mul_left_right, Nat.gcd_comm, ih, ← Nat.gcd_rec]

lemma exists_bezout_mersenne {α : Type*} [DecidableEq α] (J : Finset α) (w : α → Nat) :
    ∃ c : α → Int, J.sum (fun i => c i * ((2 ^ (w i) - 1 : Nat) : Int)) =
      ((2 ^ (J.gcd w) - 1 : Nat) : Int) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 0, by simp⟩
  | @insert i S hi ih =>
    rcases ih with ⟨cS, hcS⟩
    let u := 2 ^ (w i) - 1
    let v := 2 ^ (S.gcd w) - 1
    have hbez : ((Nat.gcd u v : Nat) : Int) = (u : Int) * Nat.gcdA u v + (v : Int) * Nat.gcdB u v :=
      Nat.gcd_eq_gcd_ab u v
    have hgcd : Nat.gcd u v = 2 ^ (Nat.gcd (w i) (S.gcd w)) - 1 :=
      gcd_two_pow_sub_one (w i) (S.gcd w)
    refine ⟨fun j => if j = i then Nat.gcdA u v else Nat.gcdB u v * cS j, ?_⟩
    rw [Finset.sum_insert hi]
    simp only [↓reduceIte]
    have hrest : S.sum (fun j => (if j = i then Nat.gcdA u v else Nat.gcdB u v * cS j) *
        ((2 ^ (w j) - 1 : Nat) : Int)) = Nat.gcdB u v * ((v : Nat) : Int) := by
      have hcongr : ∀ j ∈ S,
          (if j = i then Nat.gcdA u v else Nat.gcdB u v * cS j) * ((2 ^ (w j) - 1 : Nat) : Int) =
          Nat.gcdB u v * (cS j * ((2 ^ (w j) - 1 : Nat) : Int)) := by
        intro j hj
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        simp [hji, mul_assoc]
      rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, hcS]
    rw [hrest]
    have hgcd_ins : (insert i S).gcd w = Nat.gcd (w i) (S.gcd w) := Finset.gcd_insert
    rw [hgcd_ins, ← hgcd, hbez]
    ring

-- ============================================================================
-- Section 5: Characterization Theorem: canRecoverB a bank ↔ badB bank = ∅
-- ============================================================================

def toggle {n : Nat} (q : Finset (Fin n)) (u : Fin n) : Finset (Fin n) :=
  if u ∈ q then q.erase u else insert u q

lemma toggle_subset {n : Nat} {q B : Finset (Fin n)} {u : Fin n}
    (hq : q ⊆ B) (hu : u ∈ B) : toggle q u ⊆ B := by
  unfold toggle
  split_ifs
  · exact (Finset.erase_subset u q).trans hq
  · exact Finset.insert_subset hu hq

lemma toggle_ne {n : Nat} (q : Finset (Fin n)) (u : Fin n) : toggle q u ≠ q := by
  unfold toggle
  split_ifs with hu
  · intro h; exact Finset.notMem_erase u q (h.symm ▸ hu)
  · intro h; exact hu (h ▸ Finset.mem_insert_self u q)

lemma mem_toggle_of_ne {n : Nat} {q : Finset (Fin n)} {u v : Fin n} (hvu : v ≠ u) :
    v ∈ toggle q u ↔ v ∈ q := by
  unfold toggle
  split_ifs
  · exact Finset.mem_erase.trans (and_iff_right hvu)
  · exact Finset.mem_insert.trans (or_iff_right hvu)

lemma diff_toggle_eq_zero_of_ne {n : Nat} {x z B : Finset (Fin n)} {u v : Fin n}
    (hvB : v ∈ B) (hvu : v ≠ u) (hxz : ¬ (v ∈ x ↔ v ∈ z)) :
    (if x ∩ B = z ∩ B then (1 : Int) else 0) -
      (if x ∩ B = toggle (z ∩ B) u then (1 : Int) else 0) = 0 := by
  have h1 : x ∩ B ≠ z ∩ B := by
    intro h
    have := Finset.ext_iff.1 h v
    simp [hvB] at this
    exact hxz this
  have h2 : x ∩ B ≠ toggle (z ∩ B) u := by
    intro h
    have := Finset.ext_iff.1 h v
    rw [mem_toggle_of_ne hvu] at this
    simp [hvB] at this
    exact hxz this
  simp [h1, h2]

lemma diff_toggle_eq_one_of_eq {n : Nat} {x z B : Finset (Fin n)} {u : Fin n}
    (h : x ∩ B = z ∩ B) :
    (if x ∩ B = z ∩ B then (1 : Int) else 0) -
      (if x ∩ B = toggle (z ∩ B) u then (1 : Int) else 0) = 1 := by
  have hne : z ∩ B ≠ toggle (z ∩ B) u := (toggle_ne (z ∩ B) u).symm
  simp [h, hne]

lemma nontree_component_delta {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) {J : Finset (Fin a)} (hJ : J ∈ componentsB bank)
    (hnt : J ∉ treesB bank) (z : Finset (Fin n)) :
    InSpan bank J (fun x => if x ∩ supportB bank J = z ∩ supportB bank J then 1 else 0) := by
  have hJne : J.Nonempty := (Finset.mem_filter.1 hJ).2.1
  have ⟨i_any, _⟩ := hJne
  have ⟨v_any, _⟩ := hne i_any
  have hn : Nonempty (Fin n) := ⟨v_any⟩
  have hJconn : Conn bank J := component_conn bank hJ
  have hle := conn_edge_le bank hJconn hJne
  have hne_eq : J.sum (fun i => (bank i).card) + 1 ≠ J.card + (supportB bank J).card := by
    intro heq
    exact hnt (Finset.mem_filter.2 ⟨hJ, heq⟩)
  have hnt' : J.card + (supportB bank J).card ≤ J.sum (fun i => (bank i).card) := by omega
  rcases nontree_orient bank hne hn J.card J rfl hJconn hJne hnt' with ⟨π, hπmem, hπcov⟩
  let f : Fin a → Finset (Fin n) → Int := fun i x =>
    (if x ∩ bank i = z ∩ bank i then (1 : Int) else 0) -
      (if x ∩ bank i = toggle (z ∩ bank i) (π i) then (1 : Int) else 0)
  have hf : ∀ i ∈ J, InSpan bank {i} (f i) := fun i hi =>
    InSpan_singleton_diff bank i Finset.inter_subset_right
      (toggle_subset Finset.inter_subset_right (hπmem i hi))
  have hprod := InSpan_prod bank J f hf
  have heq : (fun x => J.prod (fun i => f i x)) =
      (fun x => if x ∩ supportB bank J = z ∩ supportB bank J then (1 : Int) else 0) := by
    ext x
    by_cases hxz : x ∩ supportB bank J = z ∩ supportB bank J
    · rw [if_pos hxz]
      apply Finset.prod_eq_one
      intro i hi
      have hbi : x ∩ bank i = z ∩ bank i := by
        ext v
        by_cases hvb : v ∈ bank i
        · have hvS : v ∈ supportB bank J := Finset.mem_biUnion.2 ⟨i, hi, hvb⟩
          have := Finset.ext_iff.1 hxz v
          simpa [hvb, hvS] using this
        · simp [hvb]
      exact diff_toggle_eq_one_of_eq hbi
    · rw [if_neg hxz]
      have hexv : ∃ v ∈ supportB bank J, ¬ (v ∈ x ↔ v ∈ z) := by
        by_contra hall
        push_neg at hall
        apply hxz
        ext v
        by_cases hvS : v ∈ supportB bank J
        · simp [hvS, hall v hvS]
        · simp [hvS]
      rcases hexv with ⟨v, hvS, hvne⟩
      rcases hπcov v hvS with ⟨i, hiJ, hvi, hπne⟩
      exact Finset.prod_eq_zero hiJ (diff_toggle_eq_zero_of_ne hvi (Ne.symm hπne) hvne)
  rwa [← heq]

lemma tree_unit_gcd_component_delta {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) {J : Finset (Fin a)} (hJ : J ∈ componentsB bank)
    (hgcd : widthGCDB bank J = 1) (z : Finset (Fin n)) :
    InSpan bank J (fun x => if x ∩ supportB bank J = z ∩ supportB bank J then 1 else 0) := by
  have hJne : J.Nonempty := (Finset.mem_filter.1 hJ).2.1
  rcases hJne with ⟨i_any, _⟩
  rcases hne i_any with ⟨v_any, _⟩
  have hn : Nonempty (Fin n) := ⟨v_any⟩
  have hJconn : Conn bank J := component_conn bank hJ
  -- For each i₀ ∈ J, construct (2^|bank i₀| - 1) * δ_{z|J} in InSpan bank J
  have hroot : ∀ i₀ ∈ J, InSpan bank J (fun x =>
      if x ∩ supportB bank J = z ∩ supportB bank J then ((2 ^ (bank i₀).card - 1 : Nat) : Int)
      else 0) := by
    intro i₀ hi₀
    rcases orient_from_root bank hJconn hn hi₀ with ⟨π, hπmem, hπcov⟩
    let f : Fin a → Finset (Fin n) → Int := fun i x =>
      if i = i₀ then
        (if x ∩ bank i = z ∩ bank i then ((2 ^ (bank i).card - 1 : Nat) : Int) else 0)
      else
        (if x ∩ bank i = z ∩ bank i then (1 : Int) else 0) -
          (if x ∩ bank i = toggle (z ∩ bank i) (π i) then (1 : Int) else 0)
    have hf : ∀ i ∈ J, InSpan bank {i} (f i) := by
      intro i hi
      by_cases hii₀ : i = i₀
      · subst hii₀
        simpa [f] using InSpan_singleton_mersenne bank i Finset.inter_subset_right
      · simpa [f, hii₀] using InSpan_singleton_diff bank i Finset.inter_subset_right
          (toggle_subset Finset.inter_subset_right (hπmem i (Finset.mem_erase.2 ⟨hii₀, hi⟩)))
    have hprod := InSpan_prod bank J f hf
    have heq : (fun x => J.prod (fun i => f i x)) =
        (fun x => if x ∩ supportB bank J = z ∩ supportB bank J then
          ((2 ^ (bank i₀).card - 1 : Nat) : Int) else 0) := by
      ext x
      by_cases hxz : x ∩ supportB bank J = z ∩ supportB bank J
      · rw [if_pos hxz]
        have hbi : ∀ i ∈ J, x ∩ bank i = z ∩ bank i := by
          intro i hi
          ext v
          by_cases hvb : v ∈ bank i
          · have hvS : v ∈ supportB bank J := Finset.mem_biUnion.2 ⟨i, hi, hvb⟩
            have := Finset.ext_iff.1 hxz v
            simpa [hvb, hvS] using this
          · simp [hvb]
        rw [← Finset.mul_prod_erase J (fun i => f i x) hi₀]
        have hrest : (J.erase i₀).prod (fun i => f i x) = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          have hii₀ : i ≠ i₀ := (Finset.mem_erase.1 hi).1
          have hiJ : i ∈ J := (Finset.mem_erase.1 hi).2
          simp only [f, hii₀, ↓reduceIte]
          exact diff_toggle_eq_one_of_eq (hbi i hiJ)
        rw [hrest, mul_one]
        simp [f, hbi i₀ hi₀]
      · rw [if_neg hxz]
        have hexv : ∃ v ∈ supportB bank J, ¬ (v ∈ x ↔ v ∈ z) := by
          by_contra hall
          push_neg at hall
          apply hxz
          ext v
          by_cases hvS : v ∈ supportB bank J
          · simp [hvS, hall v hvS]
          · simp [hvS]
        rcases hexv with ⟨v, hvS, hvne⟩
        by_cases hvi₀ : v ∈ bank i₀
        · apply Finset.prod_eq_zero hi₀
          have hne_i0 : x ∩ bank i₀ ≠ z ∩ bank i₀ := by
            intro h; have := Finset.ext_iff.1 h v; simp [hvi₀] at this; exact hvne this
          simp [f, hne_i0]
        · rcases hπcov v (Finset.mem_sdiff.2 ⟨hvS, hvi₀⟩) with ⟨i, hi, hvi, hπne⟩
          rcases Finset.mem_erase.1 hi with ⟨hii₀, hiJ⟩
          apply Finset.prod_eq_zero hiJ
          simp only [f, hii₀, ↓reduceIte]
          exact diff_toggle_eq_zero_of_ne hvi (Ne.symm hπne) hvne
    rwa [← heq]
  -- Combine via Mersenne Bezout
  rcases exists_bezout_mersenne J (fun i => (bank i).card) with ⟨α, hα⟩
  have hsum := InSpan_sum bank J J (fun i x => α i *
    (if x ∩ supportB bank J = z ∩ supportB bank J then ((2 ^ (bank i).card - 1 : Nat) : Int) else 0))
    (fun i hi => InSpan_smul (α i) (hroot i hi))
  have heq : (fun x => J.sum (fun i => α i *
      (if x ∩ supportB bank J = z ∩ supportB bank J then
        ((2 ^ (bank i).card - 1 : Nat) : Int) else 0))) =
      (fun x => if x ∩ supportB bank J = z ∩ supportB bank J then 1 else 0) := by
    ext x
    by_cases hxz : x ∩ supportB bank J = z ∩ supportB bank J
    · simp only [hxz, ↓reduceIte]
      rw [hα]
      change ((2 ^ (widthGCDB bank J) - 1 : Nat) : Int) = 1
      rw [hgcd]; norm_num
    · simp [hxz]
  rwa [← heq]

lemma widthGCDB_pos {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) {J : Finset (Fin a)} (hJne : J.Nonempty) :
    1 ≤ widthGCDB bank J := by
  by_contra hlt
  have h0 : widthGCDB bank J = 0 := by omega
  rcases hJne with ⟨i, hi⟩
  have h0' : (bank i).card = 0 := (Finset.gcd_eq_zero_iff.1 h0) i hi
  exact (hne i).ne_empty (Finset.card_eq_zero.1 h0')

lemma badB_empty_imp_canRecoverB {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) (hcov : ∀ j : Fin n, ∃ i : Fin a, j ∈ bank i)
    (hbad : badB bank = ∅) : canRecoverB a bank := by
  apply InSpan_univ_imp_canRecover
  intro z
  have hcomp : ∀ J ∈ componentsB bank,
      InSpan bank J (fun x => if x ∩ supportB bank J = z ∩ supportB bank J then 1 else 0) := by
    intro J hJ
    by_cases htree : J ∈ treesB bank
    · have hnb : J ∉ badB bank := by rw [hbad]; exact Finset.notMem_empty J
      have hle : widthGCDB bank J ≤ 1 := by
        by_contra hgt
        exact hnb (Finset.mem_filter.2 ⟨htree, by omega⟩)
      have hpos : 1 ≤ widthGCDB bank J := widthGCDB_pos bank hne (Finset.mem_filter.1 hJ).2.1
      exact tree_unit_gcd_component_delta bank hne hJ (by omega) z
    · exact nontree_component_delta bank hne hJ htree z
  have hdisj : Set.PairwiseDisjoint (componentsB bank : Set (Finset (Fin a))) id :=
    fun J1 h1 J2 h2 hne' => componentsB_disjoint bank h1 h2 hne'
  have hbu := InSpan_biUnion bank (componentsB bank) hdisj
    (fun J x => if x ∩ supportB bank J = z ∩ supportB bank J then 1 else 0) hcomp
  rw [componentsB_biUnion_id bank] at hbu
  have heq : (fun x => (componentsB bank).prod
      (fun J => if x ∩ supportB bank J = z ∩ supportB bank J then (1 : Int) else 0)) =
      (fun x => if x = z then 1 else 0) := by
    ext x
    by_cases hxz : x = z
    · subst hxz; simp
    · rw [if_neg hxz]
      have hexv : ∃ v : Fin n, ¬ (v ∈ x ↔ v ∈ z) := by
        by_contra hall; push_neg at hall
        exact hxz (Finset.ext hall)
      rcases hexv with ⟨v, hvne⟩
      have hvU : v ∈ (componentsB bank).biUnion (supportB bank) := by
        rw [componentsB_biUnion_support bank hcov]; exact Finset.mem_univ v
      rcases Finset.mem_biUnion.1 hvU with ⟨J, hJ, hvJ⟩
      apply Finset.prod_eq_zero hJ
      have hneJ : x ∩ supportB bank J ≠ z ∩ supportB bank J := by
        intro h; have := Finset.ext_iff.1 h v; simp [hvJ] at this; exact hvne this
      simp [hneJ]
  rwa [← heq]

-- Necessity: exceptional frequency S(J) = vertices of even degree in tree J
def evenDegSet {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a)) : Finset (Fin n) :=
  (supportB bank J).filter (fun v => (J.filter (fun i => v ∈ bank i)).card % 2 = 0)

def treeCharSum {n a : Nat} (bank : Fin a → Finset (Fin n)) (J : Finset (Fin a))
    (p : Fin a → Finset (Fin n)) : Int :=
  (supportB bank J).powerset.sum (fun x =>
    (-1 : Int) ^ (x ∩ evenDegSet bank J).card *
      (if ∀ i ∈ J, x ∩ bank i ≠ p i then (1 : Int) else 0))

lemma tree_char_sum_dvd {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) (g : Nat) (hg : 1 ≤ g) :
    ∀ k, ∀ J : Finset (Fin a), J.card = k → Conn bank J → J.Nonempty →
      J.sum (fun i => (bank i).card) + 1 = J.card + (supportB bank J).card →
      (∀ i ∈ J, g ∣ (bank i).card) →
      ∀ p : Fin a → Finset (Fin n), (∀ i ∈ J, p i ⊆ bank i) →
      ((2 ^ g - 1 : Nat) : Int) ∣ treeCharSum bank J p := by
  classical
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro J hJcard hJconn hJne hJtree hgdvd p hp
    by_cases hk1 : J.card = 1
    · rcases Finset.card_eq_one.1 hk1 with ⟨i₀, rfl⟩
      have hSempty : evenDegSet bank {i₀} = ∅ := by
        ext v
        simp only [evenDegSet, supportB, Finset.mem_filter, Finset.biUnion_singleton,
          Finset.notMem_empty, iff_false, not_and]
        intro hv
        have hv' : v ∈ bank i₀ := by simpa [Finset.mem_biUnion] using hv
        have : ({i₀} : Finset (Fin a)).filter (fun i => v ∈ bank i) = {i₀} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_singleton]
          exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hv'⟩⟩
        rw [this]; simp
      unfold treeCharSum
      rw [hSempty]
      have hsup : supportB bank {i₀} = bank i₀ := by simp [supportB]
      rw [hsup]
      have hsimp : (bank i₀).powerset.sum (fun x =>
          (-1 : Int) ^ (x ∩ ∅).card *
            (if ∀ i ∈ ({i₀} : Finset (Fin a)), x ∩ bank i ≠ p i then (1 : Int) else 0)) =
          ((2 ^ (bank i₀).card - 1 : Nat) : Int) := by
        have hcongr : ∀ x ∈ (bank i₀).powerset,
            (-1 : Int) ^ (x ∩ ∅).card *
              (if ∀ i ∈ ({i₀} : Finset (Fin a)), x ∩ bank i ≠ p i then (1 : Int) else 0) =
            if x ≠ p i₀ then (1 : Int) else 0 := by
          intro x hx
          have hxsub : x ⊆ bank i₀ := Finset.mem_powerset.1 hx
          have hxi : x ∩ bank i₀ = x := Finset.inter_eq_left.2 hxsub
          simp [hxi]
        rw [Finset.sum_congr rfl hcongr, Finset.sum_boole]
        have hfilt : (bank i₀).powerset.filter (fun x => x ≠ p i₀) =
            (bank i₀).powerset.erase (p i₀) := by
          ext x; simp [Finset.mem_filter, Finset.mem_erase, and_comm]
        rw [hfilt, Finset.card_erase_of_mem (Finset.mem_powerset.2 (hp i₀ (Finset.mem_singleton_self i₀))),
          Finset.card_powerset]
      rw [hsimp]
      rcases hgdvd i₀ (Finset.mem_singleton_self i₀) with ⟨q, hq⟩
      have hdvdNat : (2 ^ g - 1) ∣ (2 ^ (bank i₀).card - 1) := by
        rw [hq, mul_comm]; exact two_pow_sub_one_dvd_mul g q
      exact Int.ofNat_dvd.2 hdvdNat
    · have hJ2 : 2 ≤ J.card := by
        have := Finset.card_pos.2 hJne; omega
      rcases tree_exists_leaf bank hJconn hJ2 hJtree with
        ⟨i₀, hi₀J, hJ'conn, hJ'ne, ⟨v₀, hv₀eq⟩, hJ'tree⟩
      let J' := J.erase i₀
      let U' := supportB bank J'
      let P := (bank i₀).erase v₀
      have hv₀_mem : v₀ ∈ bank i₀ ∩ U' := by rw [hv₀eq]; exact Finset.mem_singleton_self v₀
      have hv₀_bi₀ : v₀ ∈ bank i₀ := (Finset.mem_inter.1 hv₀_mem).1
      have hv₀_U' : v₀ ∈ U' := (Finset.mem_inter.1 hv₀_mem).2
      have hdisjPU' : Disjoint P U' := by
        rw [Finset.disjoint_left]
        intro w hwP hwU'
        rcases Finset.mem_erase.1 hwP with ⟨hwne, hwb⟩
        have : w ∈ bank i₀ ∩ U' := Finset.mem_inter.2 ⟨hwb, hwU'⟩
        rw [hv₀eq, Finset.mem_singleton] at this
        exact hwne this
      have hUeq : supportB bank J = U' ∪ P := by
        have hJins : insert i₀ J' = J := Finset.insert_erase hi₀J
        rw [← hJins, supportB_insert]
        ext w
        simp only [Finset.mem_union, P, Finset.mem_erase]
        constructor
        · rintro (hwb | hwU')
          · by_cases hw : w = v₀
            · exact Or.inl (hw ▸ hv₀_U')
            · exact Or.inr ⟨hw, hwb⟩
          · exact Or.inl hwU'
        · rintro (hwU' | ⟨_, hwb⟩)
          · exact Or.inr hwU'
          · exact Or.inl hwb
      -- Compare evenDegSet bank J and evenDegSet bank J'
      have hS_P : Disjoint P (evenDegSet bank J) := by
        rw [Finset.disjoint_left]
        intro w hwP hwS
        rcases Finset.mem_erase.1 hwP with ⟨_, hwb⟩
        have hwU' : w ∉ U' := Finset.disjoint_left.1 hdisjPU' hwP
        have hfilt : J.filter (fun i => w ∈ bank i) = {i₀} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hiJ, hwi⟩
            by_contra hii₀
            exact hwU' (Finset.mem_biUnion.2 ⟨i, Finset.mem_erase.2 ⟨hii₀, hiJ⟩, hwi⟩)
          · rintro rfl; exact ⟨hi₀J, hwb⟩
        have hev := (Finset.mem_filter.1 hwS).2
        rw [hfilt] at hev
        simp at hev
      have hS_U' : ∀ w ∈ U', w ≠ v₀ → (w ∈ evenDegSet bank J ↔ w ∈ evenDegSet bank J') := by
        intro w hwU' hwne
        have hwb : w ∉ bank i₀ := by
          intro h
          have : w ∈ bank i₀ ∩ U' := Finset.mem_inter.2 ⟨h, hwU'⟩
          rw [hv₀eq, Finset.mem_singleton] at this
          exact hwne this
        have hfilt : J.filter (fun i => w ∈ bank i) = J'.filter (fun i => w ∈ bank i) := by
          ext i
          simp only [Finset.mem_filter, J', Finset.mem_erase]
          constructor
          · rintro ⟨hiJ, hwi⟩
            exact ⟨⟨fun h => hwb (h ▸ hwi), hiJ⟩, hwi⟩
          · rintro ⟨⟨_, hiJ⟩, hwi⟩
            exact ⟨hiJ, hwi⟩
        have hwU'' : w ∈ supportB bank J' := hwU'
        simp only [evenDegSet, Finset.mem_filter, hUeq, Finset.mem_union, hwU', hwU'', true_or,
          true_and, hfilt]
      have hS_v₀ : v₀ ∈ evenDegSet bank J ↔ v₀ ∉ evenDegSet bank J' := by
        have hfilt : J.filter (fun i => v₀ ∈ bank i) =
            insert i₀ (J'.filter (fun i => v₀ ∈ bank i)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_insert, J', Finset.mem_erase]
          constructor
          · rintro ⟨hiJ, hvi⟩
            by_cases h : i = i₀
            · exact Or.inl h
            · exact Or.inr ⟨⟨h, hiJ⟩, hvi⟩
          · rintro (rfl | ⟨⟨_, hiJ⟩, hvi⟩)
            · exact ⟨hi₀J, hv₀_bi₀⟩
            · exact ⟨hiJ, hvi⟩
        have hnotmem : i₀ ∉ J'.filter (fun i => v₀ ∈ bank i) := by
          simp [J']
        have hcard_f : (J.filter (fun i => v₀ ∈ bank i)).card =
            (J'.filter (fun i => v₀ ∈ bank i)).card + 1 := by
          rw [hfilt, Finset.card_insert_of_notMem hnotmem]
        have hv₀_U'' : v₀ ∈ supportB bank J' := hv₀_U'
        simp only [evenDegSet, Finset.mem_filter, hUeq, Finset.mem_union, hv₀_U', hv₀_U'', true_or,
          true_and, hcard_f]
        omega
      -- Sign relation for x' ⊆ U' and y ⊆ P
      have hsign : ∀ x' ⊆ U', ∀ y ⊆ P,
          (-1 : Int) ^ ((x' ∪ y) ∩ evenDegSet bank J).card =
          (-1 : Int) ^ (x' ∩ evenDegSet bank J').card * (if v₀ ∈ x' then (-1 : Int) else 1) := by
        intro x' hx' y hy
        have hyS : y ∩ evenDegSet bank J = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.1 (hdisjPU'.mono_left hy |>.symm |>.symm |> fun _ =>
            hS_P.mono_left hy)
        have hunion_int : (x' ∪ y) ∩ evenDegSet bank J = x' ∩ evenDegSet bank J := by
          rw [Finset.union_inter_distrib_right, hyS, Finset.union_empty]
        rw [hunion_int]
        by_cases hvx : v₀ ∈ x'
        · rw [if_pos hvx]
          by_cases hvSJ' : v₀ ∈ evenDegSet bank J'
          · have hvSJ : v₀ ∉ evenDegSet bank J := fun h => (hS_v₀.1 h) hvSJ'
            have heq_set : x' ∩ evenDegSet bank J' = insert v₀ (x' ∩ evenDegSet bank J) := by
              ext w
              simp only [Finset.mem_inter, Finset.mem_insert]
              by_cases hwv : w = v₀
              · subst hwv; simp [hvx, hvSJ', hvSJ]
              · constructor
                · rintro ⟨hwx, hwS⟩
                  exact Or.inr ⟨hwx, (hS_U' w (hx' hwx) hwv).2 hwS⟩
                · rintro (rfl | ⟨hwx, hwS⟩)
                  · exact False.elim (hwv rfl)
                  · exact ⟨hwx, (hS_U' w (hx' hwx) hwv).1 hwS⟩
            rw [heq_set, Finset.card_insert_of_notMem (by simp [hvSJ]), pow_succ]
            ring
          · have hvSJ : v₀ ∈ evenDegSet bank J := hS_v₀.2 hvSJ'
            have heq_set : x' ∩ evenDegSet bank J = insert v₀ (x' ∩ evenDegSet bank J') := by
              ext w
              simp only [Finset.mem_inter, Finset.mem_insert]
              by_cases hwv : w = v₀
              · subst hwv; simp [hvx, hvSJ', hvSJ]
              · constructor
                · rintro ⟨hwx, hwS⟩
                  exact Or.inr ⟨hwx, (hS_U' w (hx' hwx) hwv).1 hwS⟩
                · rintro (rfl | ⟨hwx, hwS⟩)
                  · exact False.elim (hwv rfl)
                  · exact ⟨hwx, (hS_U' w (hx' hwx) hwv).2 hwS⟩
            rw [heq_set, Finset.card_insert_of_notMem (by simp [hvSJ']), pow_succ]
        · rw [if_neg hvx, mul_one]
          congr 1
          congr 1
          ext w
          simp only [Finset.mem_inter]
          by_cases hwx : w ∈ x'
          · have hwv : w ≠ v₀ := fun h => hvx (h ▸ hwx)
            simp [hwx, hS_U' w (hx' hwx) hwv]
          · simp [hwx]
      -- Split treeCharSum over (U' ∪ P).powerset ≃ U'.powerset ×ˢ P.powerset
      have hsplit : treeCharSum bank J p =
          U'.powerset.sum (fun x' =>
            (-1 : Int) ^ (x' ∩ evenDegSet bank J').card *
              (if ∀ i ∈ J', x' ∩ bank i ≠ p i then (1 : Int) else 0) *
              ((if v₀ ∈ x' then (-1 : Int) else 1) *
                P.powerset.sum (fun y =>
                  if (x' ∪ y) ∩ bank i₀ ≠ p i₀ then (1 : Int) else 0))) := by
        unfold treeCharSum
        rw [hUeq]
        have hbij : (U' ∪ P).powerset.sum (fun x =>
            (-1 : Int) ^ (x ∩ evenDegSet bank J).card *
              (if ∀ i ∈ J, x ∩ bank i ≠ p i then (1 : Int) else 0)) =
            (U'.powerset ×ˢ P.powerset).sum (fun xy =>
              (-1 : Int) ^ ((xy.1 ∪ xy.2) ∩ evenDegSet bank J).card *
                (if ∀ i ∈ J, (xy.1 ∪ xy.2) ∩ bank i ≠ p i then (1 : Int) else 0)) := by
          symm
          refine Finset.sum_bij (fun xy _ => xy.1 ∪ xy.2) ?_ ?_ ?_ ?_
          · rintro ⟨x', y⟩ hxy
            rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hxy
            exact Finset.mem_powerset.2 (Finset.union_subset_union hxy.1 hxy.2)
          · rintro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 heq
            rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at h1 h2
            ext w
            · constructor
              · intro hw
                have : w ∈ x2 ∪ y2 := heq ▸ Finset.mem_union_left y1 hw
                rcases Finset.mem_union.1 this with h | h
                · exact h
                · exact False.elim (Finset.disjoint_left.1 hdisjPU' (h2.2 h) (h1.1 hw))
              · intro hw
                have : w ∈ x1 ∪ y1 := heq.symm ▸ Finset.mem_union_left y2 hw
                rcases Finset.mem_union.1 this with h | h
                · exact h
                · exact False.elim (Finset.disjoint_left.1 hdisjPU' (h1.2 h) (h2.1 hw))
            · constructor
              · intro hw
                have : w ∈ x2 ∪ y2 := heq ▸ Finset.mem_union_right x1 hw
                rcases Finset.mem_union.1 this with h | h
                · exact False.elim (Finset.disjoint_left.1 hdisjPU' (h1.2 hw) (h2.1 h))
                · exact h
              · intro hw
                have : w ∈ x1 ∪ y1 := heq.symm ▸ Finset.mem_union_right x2 hw
                rcases Finset.mem_union.1 this with h | h
                · exact False.elim (Finset.disjoint_left.1 hdisjPU' (h2.2 hw) (h1.1 h))
                · exact h
          · intro x hx
            rw [Finset.mem_powerset] at hx
            refine ⟨(x ∩ U', x ∩ P), ?_, ?_⟩
            · exact Finset.mem_product.2 ⟨Finset.mem_powerset.2 Finset.inter_subset_right,
                Finset.mem_powerset.2 Finset.inter_subset_right⟩
            · rw [← Finset.inter_union_distrib_left]
              exact Finset.inter_eq_left.2 hx
          · intro _ _; rfl
        rw [hbij, Finset.sum_product]
        apply Finset.sum_congr rfl
        intro x' hx'
        have hx'sub : x' ⊆ U' := Finset.mem_powerset.1 hx'
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        have hysub : y ⊆ P := Finset.mem_powerset.1 hy
        rw [hsign x' hx'sub y hysub]
        have hcond : (∀ i ∈ J, (x' ∪ y) ∩ bank i ≠ p i) ↔
            (∀ i ∈ J', x' ∩ bank i ≠ p i) ∧ (x' ∪ y) ∩ bank i₀ ≠ p i₀ := by
          have hJins : insert i₀ J' = J := Finset.insert_erase hi₀J
          rw [← hJins]
          simp only [Finset.mem_insert, forall_eq_or_imp]
          have hrest : (∀ i ∈ J', (x' ∪ y) ∩ bank i ≠ p i) ↔ (∀ i ∈ J', x' ∩ bank i ≠ p i) := by
            apply forall₂_congr
            intro i hi
            have hbiU' : bank i ⊆ U' := Finset.subset_biUnion_of_mem bank hi
            have hybi : y ∩ bank i = ∅ :=
              Finset.disjoint_iff_inter_eq_empty.1 (hdisjPU'.mono hysub hbiU')
            rw [Finset.union_inter_distrib_right, hybi, Finset.union_empty]
          rw [hrest, and_comm]
        dsimp only
        by_cases h1 : ∀ i ∈ J', x' ∩ bank i ≠ p i <;>
          by_cases h2 : (x' ∪ y) ∩ bank i₀ ≠ p i₀
        · rw [if_pos (hcond.2 ⟨h1, h2⟩), if_pos h1, if_pos h2]; ring
        · rw [if_neg (fun h => h2 (hcond.1 h).2), if_pos h1, if_neg h2]; ring
        · rw [if_neg (fun h => h1 (hcond.1 h).1), if_neg h1, if_pos h2]; ring
        · rw [if_neg (fun h => h1 (hcond.1 h).1), if_neg h1, if_neg h2]; ring
      -- Evaluate inner y-sum modulo 2^g - 1
      let w := (bank i₀).card
      have hPcard : P.card + 1 = w := by
        have := Finset.card_erase_add_one hv₀_bi₀; exact this
      let sp : Int := if v₀ ∈ p i₀ then 1 else -1
      have hinner : ∀ x' ∈ U'.powerset,
          ((2 ^ g - 1 : Nat) : Int) ∣
            (2 * ((if v₀ ∈ x' then (-1 : Int) else 1) *
              P.powerset.sum (fun y => if (x' ∪ y) ∩ bank i₀ ≠ p i₀ then (1 : Int) else 0)) - sp) := by
        intro x' hx'
        have hx'sub : x' ⊆ U' := Finset.mem_powerset.1 hx'
        have hpi₀_sub : p i₀ ⊆ bank i₀ := hp i₀ hi₀J
        have hpi₀_P : (p i₀).erase v₀ ∈ P.powerset :=
          Finset.mem_powerset.2 (Finset.erase_subset_erase v₀ hpi₀_sub)
        have hiff : ∀ y ∈ P.powerset,
            (x' ∪ y) ∩ bank i₀ = p i₀ ↔ ((v₀ ∈ x' ↔ v₀ ∈ p i₀) ∧ y = (p i₀).erase v₀) := by
          intro y hy
          have hysub : y ⊆ P := Finset.mem_powerset.1 hy
          have hv₀y : v₀ ∉ y := fun h => (Finset.notMem_erase v₀ (bank i₀)) (hysub h)
          have hbi₀_eq : bank i₀ = insert v₀ P := (Finset.insert_erase hv₀_bi₀).symm
          constructor
          · intro heq
            refine ⟨?_, ?_⟩
            · have := Finset.ext_iff.1 heq v₀
              simpa [hv₀_bi₀, hv₀y] using this
            · ext u
              by_cases huv : u = v₀
              · subst huv; simp [hv₀y]
              · have := Finset.ext_iff.1 heq u
                by_cases huP : u ∈ P
                · have huU' : u ∉ U' := Finset.disjoint_left.1 hdisjPU' huP
                  have hux' : u ∉ x' := fun h => huU' (hx'sub h)
                  have hub : u ∈ bank i₀ := (Finset.mem_erase.1 huP).2
                  simpa [huv, hux', hub] using this
                · have huy : u ∉ y := fun h => huP (hysub h)
                  have hub : u ∉ bank i₀ := fun h => huP (Finset.mem_erase.2 ⟨huv, h⟩)
                  have hup : u ∉ p i₀ := fun h => hub (hpi₀_sub h)
                  simp [huv, huy, hup]
          · rintro ⟨hviff, rfl⟩
            ext u
            by_cases huv : u = v₀
            · subst huv; simp [hv₀_bi₀, hviff]
            · by_cases huP : u ∈ P
              · have huU' : u ∉ U' := Finset.disjoint_left.1 hdisjPU' huP
                have hux' : u ∉ x' := fun h => huU' (hx'sub h)
                have hub : u ∈ bank i₀ := (Finset.mem_erase.1 huP).2
                simp [huv, hux', hub]
              · have hub : u ∉ bank i₀ := fun h => huP (Finset.mem_erase.2 ⟨huv, h⟩)
                have hup : u ∉ p i₀ := fun h => hub (hpi₀_sub h)
                simp [huv, hub, hup]
        have hdvd_w : ((2 ^ g - 1 : Nat) : Int) ∣ ((2 ^ w - 1 : Nat) : Int) := by
          rcases hgdvd i₀ hi₀J with ⟨q, hq⟩
          have hdvdNat : (2 ^ g - 1) ∣ (2 ^ w - 1) := by
            change (2 ^ g - 1) ∣ (2 ^ (bank i₀).card - 1)
            rw [hq, mul_comm]; exact two_pow_sub_one_dvd_mul g q
          exact Int.ofNat_dvd.2 hdvdNat
        have h2w : (2 : Int) * (2 ^ P.card : Int) = ((2 ^ w : Nat) : Int) := by
          have : 2 * 2 ^ P.card = 2 ^ w := by rw [← hPcard, pow_succ']
          exact_mod_cast this
        have h1w : (1 : Nat) ≤ 2 ^ w := Nat.one_le_two_pow
        have hw_cast : ((2 ^ w - 1 : Nat) : Int) = ((2 ^ w : Nat) : Int) - 1 := by
          rw [Nat.cast_sub h1w]; simp
        by_cases hviff : v₀ ∈ x' ↔ v₀ ∈ p i₀
        · have hysum : P.powerset.sum (fun y => if (x' ∪ y) ∩ bank i₀ ≠ p i₀ then (1 : Int) else 0) =
              (2 ^ P.card : Int) - 1 := by
            have hcongr : ∀ y ∈ P.powerset,
                (if (x' ∪ y) ∩ bank i₀ ≠ p i₀ then (1 : Int) else 0) =
                if y ≠ (p i₀).erase v₀ then (1 : Int) else 0 := by
              intro y hy
              have := hiff y hy
              simp [this, hviff]
            rw [Finset.sum_congr rfl hcongr, Finset.sum_boole]
            have hfilt : P.powerset.filter (fun y => y ≠ (p i₀).erase v₀) =
                P.powerset.erase ((p i₀).erase v₀) := by
              ext y; simp [Finset.mem_filter, Finset.mem_erase, and_comm]
            rw [hfilt, Finset.card_erase_of_mem hpi₀_P, Finset.card_powerset]
            have h1P : 1 ≤ 2 ^ P.card := Nat.one_le_two_pow
            rw [Nat.cast_sub h1P]; push_cast; rfl
          rw [hysum]
          by_cases hvx : v₀ ∈ x'
          · have hvp : v₀ ∈ p i₀ := hviff.1 hvx
            have heq : 2 * ((if v₀ ∈ x' then (-1 : Int) else 1) * ((2 ^ P.card : Int) - 1)) - sp =
                -(((2 ^ w - 1 : Nat) : Int)) := by
              simp only [hvx, hvp, ↓reduceIte, sp]
              rw [hw_cast]; linarith
            rw [heq]; exact dvd_neg.2 hdvd_w
          · have hvp : v₀ ∉ p i₀ := fun h => hvx (hviff.2 h)
            have heq : 2 * ((if v₀ ∈ x' then (-1 : Int) else 1) * ((2 ^ P.card : Int) - 1)) - sp =
                ((2 ^ w - 1 : Nat) : Int) := by
              simp only [hvx, hvp, ↓reduceIte, sp]
              rw [hw_cast]; linarith
            rw [heq]; exact hdvd_w
        · have hysum : P.powerset.sum (fun y => if (x' ∪ y) ∩ bank i₀ ≠ p i₀ then (1 : Int) else 0) =
              (2 ^ P.card : Int) := by
            have hcongr : ∀ y ∈ P.powerset,
                (if (x' ∪ y) ∩ bank i₀ ≠ p i₀ then (1 : Int) else 0) = 1 := by
              intro y hy
              have hne' : (x' ∪ y) ∩ bank i₀ ≠ p i₀ := fun h => hviff ((hiff y hy).1 h).1
              simp [hne']
            rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul, mul_one,
              Finset.card_powerset]
            push_cast; rfl
          rw [hysum]
          by_cases hvx : v₀ ∈ x'
          · have hvp : v₀ ∉ p i₀ := fun h => hviff ⟨fun _ => h, fun _ => hvx⟩
            have heq : 2 * ((if v₀ ∈ x' then (-1 : Int) else 1) * (2 ^ P.card : Int)) - sp =
                -(((2 ^ w - 1 : Nat) : Int)) := by
              simp only [hvx, hvp, ↓reduceIte, sp]
              rw [hw_cast]; linarith
            rw [heq]; exact dvd_neg.2 hdvd_w
          · have hvp : v₀ ∈ p i₀ := by tauto
            have heq : 2 * ((if v₀ ∈ x' then (-1 : Int) else 1) * (2 ^ P.card : Int)) - sp =
                ((2 ^ w - 1 : Nat) : Int) := by
              simp only [hvx, hvp, ↓reduceIte, sp]
              rw [hw_cast]; linarith
            rw [heq]; exact hdvd_w
      -- Combine: (2^g - 1) ∣ (2 * treeCharSum J p - sp * treeCharSum J' p)
      have hdiff_dvd : ((2 ^ g - 1 : Nat) : Int) ∣
          (2 * treeCharSum bank J p - sp * treeCharSum bank J' p) := by
        rw [hsplit]
        have hrhs : sp * treeCharSum bank J' p =
            U'.powerset.sum (fun x' =>
              (-1 : Int) ^ (x' ∩ evenDegSet bank J').card *
                (if ∀ i ∈ J', x' ∩ bank i ≠ p i then (1 : Int) else 0) * sp) := by
          unfold treeCharSum
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x' _; ring
        rw [hrhs, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.dvd_sum
        intro x' hx'
        have hfac :
            2 * ((-1 : Int) ^ (x' ∩ evenDegSet bank J').card *
                (if ∀ i ∈ J', x' ∩ bank i ≠ p i then (1 : Int) else 0) *
                ((if v₀ ∈ x' then (-1 : Int) else 1) *
                  P.powerset.sum (fun y => if (x' ∪ y) ∩ bank i₀ ≠ p i₀ then (1 : Int) else 0))) -
              (-1 : Int) ^ (x' ∩ evenDegSet bank J').card *
                (if ∀ i ∈ J', x' ∩ bank i ≠ p i then (1 : Int) else 0) * sp =
            ((-1 : Int) ^ (x' ∩ evenDegSet bank J').card *
              (if ∀ i ∈ J', x' ∩ bank i ≠ p i then (1 : Int) else 0)) *
            (2 * ((if v₀ ∈ x' then (-1 : Int) else 1) *
              P.powerset.sum (fun y => if (x' ∪ y) ∩ bank i₀ ≠ p i₀ then (1 : Int) else 0)) - sp) := by
          ring
        rw [hfac]
        exact dvd_mul_of_dvd_right (hinner x' hx') _
      -- Apply IH to J'
      have hJ'lt : J'.card < k := by
        have := Finset.card_erase_lt_of_mem hi₀J
        change (J.erase i₀).card < k
        omega
      have hih : ((2 ^ g - 1 : Nat) : Int) ∣ treeCharSum bank J' p :=
        ih J'.card hJ'lt J' rfl hJ'conn hJ'ne hJ'tree
          (fun i hi => hgdvd i (Finset.mem_of_mem_erase hi))
          p (fun i hi => hp i (Finset.mem_of_mem_erase hi))
      have h2dvd : ((2 ^ g - 1 : Nat) : Int) ∣ 2 * treeCharSum bank J p := by
        have hsum := dvd_add hdiff_dvd (dvd_mul_of_dvd_right hih sp)
        simpa using hsum
      -- Cancel factor of 2 using 2 * 2^(g-1) - (2^g - 1) = 1
      have h1g : 1 ≤ 2 ^ g := Nat.one_le_two_pow
      have hbez2 : (2 : Int) * ((2 ^ (g - 1) : Nat) : Int) - ((2 ^ g - 1 : Nat) : Int) = 1 := by
        have hpow : 2 * 2 ^ (g - 1) = 2 ^ g := by
          rw [← pow_succ', Nat.sub_add_cancel hg]
        have hpowZ : (2 : Int) * ((2 ^ (g - 1) : Nat) : Int) = ((2 ^ g : Nat) : Int) := by
          exact_mod_cast hpow
        have hsubZ : ((2 ^ g - 1 : Nat) : Int) = ((2 ^ g : Nat) : Int) - 1 := by
          rw [Nat.cast_sub h1g]; simp
        linarith
      have hident : treeCharSum bank J p =
          ((2 ^ (g - 1) : Nat) : Int) * (2 * treeCharSum bank J p) -
            ((2 ^ g - 1 : Nat) : Int) * treeCharSum bank J p := by
        calc treeCharSum bank J p
            = 1 * treeCharSum bank J p := (one_mul _).symm
          _ = (2 * ((2 ^ (g - 1) : Nat) : Int) - ((2 ^ g - 1 : Nat) : Int)) *
                treeCharSum bank J p := by rw [hbez2]
          _ = _ := by ring
      rw [hident]
      exact dvd_sub (dvd_mul_of_dvd_right h2dvd _) (dvd_mul_right _ _)

lemma canRecoverB_imp_badB_empty {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) (hrec : canRecoverB a bank) : badB bank = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro J hJbad
  have hJtree_mem : J ∈ treesB bank := (Finset.mem_filter.1 hJbad).1
  have hg_gt : 1 < widthGCDB bank J := (Finset.mem_filter.1 hJbad).2
  have hJcomp : J ∈ componentsB bank := (Finset.mem_filter.1 hJtree_mem).1
  have hJtree : J.sum (fun i => (bank i).card) + 1 = J.card + (supportB bank J).card :=
    (Finset.mem_filter.1 hJtree_mem).2
  have hJne : J.Nonempty := (Finset.mem_filter.1 hJcomp).2.1
  have hJcl : closedB bank J = true := (Finset.mem_filter.1 hJcomp).2.2.1
  have hJconn : Conn bank J := component_conn bank hJcomp
  let g := widthGCDB bank J
  have hgdvd : ∀ i ∈ J, g ∣ (bank i).card := fun i hi => Finset.gcd_dvd hi
  rcases hrec ∅ with ⟨c, hc⟩
  let patterns := (Finset.univ : Finset (Fin a → Finset (Fin n))).filter
    (fun p => ∀ i, p i ⊆ bank i)
  -- Sum (-1)^|x ∩ evenDegSet J| * δ_∅(x) over x ∈ (supportB bank J).powerset
  have hrhs : (supportB bank J).powerset.sum (fun x =>
      (-1 : Int) ^ (x ∩ evenDegSet bank J).card * (if x = ∅ then (1 : Int) else 0)) = 1 := by
    have hcongr : ∀ x ∈ (supportB bank J).powerset,
        (-1 : Int) ^ (x ∩ evenDegSet bank J).card * (if x = ∅ then (1 : Int) else 0) =
        if x = ∅ then (1 : Int) else 0 := by
      intro x _; by_cases hx : x = ∅ <;> simp [hx]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
    simp
  have hlhs : (supportB bank J).powerset.sum (fun x =>
      (-1 : Int) ^ (x ∩ evenDegSet bank J).card * (if x = ∅ then (1 : Int) else 0)) =
      patterns.sum (fun p =>
        (c p * (if ∀ i ∉ J, (∅ : Finset (Fin n)) ≠ p i then (1 : Int) else 0)) *
          treeCharSum bank J p) := by
    have hstep1 : ∀ x ∈ (supportB bank J).powerset,
        (-1 : Int) ^ (x ∩ evenDegSet bank J).card * (if x = ∅ then (1 : Int) else 0) =
        patterns.sum (fun p =>
          (-1 : Int) ^ (x ∩ evenDegSet bank J).card *
            (if ∀ i, x ∩ bank i ≠ p i then c p else 0)) := by
      intro x _
      rw [← hc x, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_congr rfl hstep1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    unfold treeCharSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hxsub : x ⊆ supportB bank J := Finset.mem_powerset.1 hx
    have hcond : (∀ i : Fin a, x ∩ bank i ≠ p i) ↔
        (∀ i ∉ J, (∅ : Finset (Fin n)) ≠ p i) ∧ (∀ i ∈ J, x ∩ bank i ≠ p i) := by
      constructor
      · intro h
        refine ⟨fun i hi => ?_, fun i _ => h i⟩
        have hdisj := closedB_disjoint_support hJcl hi
        have hxbi : x ∩ bank i = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.1 (hdisj.mono_left hxsub)
        rw [← hxbi]; exact h i
      · rintro ⟨h1, h2⟩ i
        by_cases hi : i ∈ J
        · exact h2 i hi
        · have hdisj := closedB_disjoint_support hJcl hi
          have hxbi : x ∩ bank i = ∅ :=
            Finset.disjoint_iff_inter_eq_empty.1 (hdisj.mono_left hxsub)
          rw [hxbi]; exact h1 i hi
    by_cases h1 : ∀ i ∉ J, (∅ : Finset (Fin n)) ≠ p i <;>
      by_cases h2 : ∀ i ∈ J, x ∩ bank i ≠ p i
    · rw [if_pos (hcond.2 ⟨h1, h2⟩), if_pos h1, if_pos h2]; ring
    · rw [if_neg (fun h => h2 (hcond.1 h).2), if_pos h1, if_neg h2]; ring
    · rw [if_neg (fun h => h1 (hcond.1 h).1), if_neg h1, if_pos h2]; ring
    · rw [if_neg (fun h => h1 (hcond.1 h).1), if_neg h1, if_neg h2]; ring
  have hdvd1 : ((2 ^ g - 1 : Nat) : Int) ∣ 1 := by
    rw [← hrhs, hlhs]
    apply Finset.dvd_sum
    intro p hp
    have hp' : ∀ i ∈ J, p i ⊆ bank i := fun i _ => (Finset.mem_filter.1 hp).2 i
    exact dvd_mul_of_dvd_right
      (tree_char_sum_dvd bank hne g (by omega) J.card J rfl hJconn hJne hJtree hgdvd p hp') _
  have hge3 : (3 : Nat) ≤ 2 ^ g - 1 := by
    have : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by omega) hg_gt
    omega
  have hle1 : 2 ^ g - 1 ≤ 1 := by
    have hnat : (2 ^ g - 1) ∣ 1 := Int.ofNat_dvd.1 hdvd1
    exact Nat.le_of_dvd (by omega) hnat
  omega

theorem canRecoverB_iff_badB_empty {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) (hcov : ∀ j : Fin n, ∃ i : Fin a, j ∈ bank i) :
    canRecoverB a bank ↔ badB bank = ∅ :=
  ⟨canRecoverB_imp_badB_empty bank hne, badB_empty_imp_canRecoverB bank hne hcov⟩

-- ============================================================================
-- Section 6: One-Step Binary Scope Addition (snocB bank e)
-- ============================================================================

def snocB {n a : Nat} (bank : Fin a → Finset (Fin n)) (e : Finset (Fin n)) :
    Fin (a + 1) → Finset (Fin n) :=
  Fin.snoc (α := fun _ => Finset (Fin n)) bank e

lemma snocB_castSucc {n a : Nat} (bank : Fin a → Finset (Fin n)) (e : Finset (Fin n)) (i : Fin a) :
    snocB bank e i.castSucc = bank i := by
  simp [snocB, Fin.snoc_castSucc]

lemma snocB_last {n a : Nat} (bank : Fin a → Finset (Fin n)) (e : Finset (Fin n)) :
    snocB bank e (Fin.last a) = e := by
  simp [snocB, Fin.snoc_last]

def consB {n s : Nat} (e : Finset (Fin n)) (extra : Fin s → Finset (Fin n)) :
    Fin (s + 1) → Finset (Fin n) :=
  Fin.cons (α := fun _ => Finset (Fin n)) e extra

def addCasesB {n t s : Nat} (scope : Fin t → Finset (Fin n)) (extra : Fin s → Finset (Fin n)) :
    Fin (t + s) → Finset (Fin n) :=
  Fin.addCases (motive := fun _ => Finset (Fin n)) scope extra


def castEmb (a : Nat) : Fin a ↪ Fin (a + 1) :=
  ⟨Fin.castSucc, Fin.castSucc_injective a⟩

def mapCastEmb (a : Nat) : Finset (Fin a) ↪ Finset (Fin (a + 1)) :=
  Finset.mapEmbedding (castEmb a) |>.toEmbedding

lemma gcd_map_emb {α β : Type*} [DecidableEq β] (s : Finset α) (e : α ↪ β) (f : β → Nat) :
    (s.map e).gcd f = s.gcd (fun x => f (e x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.map_insert, Finset.gcd_insert, Finset.gcd_insert, ih]

lemma subset_sdiff_union_aux {α : Type*} [DecidableEq α] (A B : Finset α) : A ⊆ (A \ B) ∪ B := by
  intro x hx
  by_cases h : x ∈ B
  · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, h⟩)

lemma snoc_reach_lift {n a : Nat} (bank : Fin a → Finset (Fin n)) (e : Finset (Fin n))
    {x y : Fin a} (h : ReachB bank x y) :
    ReachB (snocB bank e) (castEmb a x) (castEmb a y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
    refine Relation.ReflTransGen.tail ih ?_
    change (snocB bank e b.castSucc ∩ snocB bank e c.castSucc).Nonempty
    rwa [snocB_castSucc, snocB_castSucc]

lemma snoc_comp_last {n a : Nat} (bank : Fin a → Finset (Fin n))
    (e : Finset (Fin n)) (u v : Fin n) (he : e = {u, v})
    (i₁ i₂ : Fin a) (hu : u ∈ bank i₁) (hv : v ∈ bank i₂) :
    compOf (snocB bank e) (Fin.last a) =
      insert (Fin.last a) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a)) := by
  have hJ₁cl : closedB bank (compOf bank i₁) = true := compOf_closedB bank i₁
  have hJ₂cl : closedB bank (compOf bank i₂) = true := compOf_closedB bank i₂
  have hbank_cast : ∀ j : Fin a, snocB bank e (castEmb a j) = bank j := fun j => snocB_castSucc bank e j
  have hbank_last : snocB bank e (Fin.last a) = e := snocB_last bank e
  have hJnew_cl : closedB (snocB bank e)
      (insert (Fin.last a) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a))) = true := by
    rw [closedB_iff]
    intro x hx y hxy
    revert hxy
    refine Fin.lastCases ?_ ?_ y
    · intro _
      exact Finset.mem_insert_self (Fin.last a) _
    · intro h hxy
      change (snocB bank e x ∩ snocB bank e (castEmb a h)).Nonempty at hxy
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_map]
      refine ⟨h, ?_, rfl⟩
      rcases Finset.mem_insert.1 hx with rfl | hxmap
      · rw [hbank_last, hbank_cast, he] at hxy
        rcases hxy with ⟨w, hw⟩
        rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw.1 with rfl | rfl
        · exact Finset.mem_union_left (compOf bank i₂)
            ((closedB_iff bank (compOf bank i₁)).1 hJ₁cl i₁ (self_mem_compOf bank i₁) h
              ⟨w, Finset.mem_inter.2 ⟨hu, hw.2⟩⟩)
        · exact Finset.mem_union_right (compOf bank i₁)
            ((closedB_iff bank (compOf bank i₂)).1 hJ₂cl i₂ (self_mem_compOf bank i₂) h
              ⟨w, Finset.mem_inter.2 ⟨hv, hw.2⟩⟩)
      · rw [Finset.mem_map] at hxmap
        rcases hxmap with ⟨j, hj, rfl⟩
        rw [hbank_cast, hbank_cast] at hxy
        rcases Finset.mem_union.1 hj with hj1 | hj2
        · exact Finset.mem_union_left _ ((closedB_iff bank _).1 hJ₁cl j hj1 h hxy)
        · exact Finset.mem_union_right _ ((closedB_iff bank _).1 hJ₂cl j hj2 h hxy)
  apply Finset.Subset.antisymm
  · intro x hx
    exact closedB_reach hJnew_cl (Finset.mem_insert_self _ _) ((mem_compOf (snocB bank e) _ x).1 hx)
  · intro x hx
    rw [mem_compOf]
    rcases Finset.mem_insert.1 hx with rfl | hxmap
    · exact ReachB_refl (snocB bank e) _
    · rw [Finset.mem_map] at hxmap
      rcases hxmap with ⟨j, hj, rfl⟩
      rcases Finset.mem_union.1 hj with hj1 | hj2
      · have h1 : ReachB (snocB bank e) (Fin.last a) (castEmb a i₁) :=
          Relation.ReflTransGen.single (by
            change (snocB bank e (Fin.last a) ∩ snocB bank e (castEmb a i₁)).Nonempty
            rw [hbank_last, hbank_cast, he]
            exact ⟨u, Finset.mem_inter.2 ⟨Finset.mem_insert_self u {v}, hu⟩⟩)
        exact ReachB_trans h1 (snoc_reach_lift bank e ((mem_compOf bank i₁ j).1 hj1))
      · have h2 : ReachB (snocB bank e) (Fin.last a) (castEmb a i₂) :=
          Relation.ReflTransGen.single (by
            change (snocB bank e (Fin.last a) ∩ snocB bank e (castEmb a i₂)).Nonempty
            rw [hbank_last, hbank_cast, he]
            exact ⟨v, Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self v), hv⟩⟩)
        exact ReachB_trans h2 (snoc_reach_lift bank e ((mem_compOf bank i₂ j).1 hj2))

lemma snoc_comp_other {n a : Nat} (bank : Fin a → Finset (Fin n))
    (e : Finset (Fin n)) (u v : Fin n) (he : e = {u, v})
    (i₁ i₂ : Fin a) (hu : u ∈ bank i₁) (hv : v ∈ bank i₂)
    {J : Finset (Fin a)} (hJ : J ∈ componentsB bank \ {compOf bank i₁, compOf bank i₂})
    {r : Fin a} (hr : r ∈ J) :
    compOf (snocB bank e) (castEmb a r) = mapCastEmb a J := by
  have hJ₁mem : compOf bank i₁ ∈ componentsB bank := compOf_mem_componentsB bank i₁
  have hJ₂mem : compOf bank i₂ ∈ componentsB bank := compOf_mem_componentsB bank i₂
  have hJ₁cl : closedB bank (compOf bank i₁) = true := compOf_closedB bank i₁
  have hJ₂cl : closedB bank (compOf bank i₂) = true := compOf_closedB bank i₂
  have hbank_cast : ∀ j : Fin a, snocB bank e (castEmb a j) = bank j := fun j => snocB_castSucc bank e j
  have hbank_last : snocB bank e (Fin.last a) = e := snocB_last bank e
  have hJmem : J ∈ componentsB bank := (Finset.mem_sdiff.1 hJ).1
  have hJnot : J ∉ ({compOf bank i₁, compOf bank i₂} : Finset (Finset (Fin a))) := (Finset.mem_sdiff.1 hJ).2
  have hJne1 : J ≠ compOf bank i₁ := fun h => hJnot (by simp [h])
  have hJne2 : J ≠ compOf bank i₂ := fun h => hJnot (by simp [h])
  have hJcl : closedB bank J = true := (Finset.mem_filter.1 hJmem).2.2.1
  have hJeq : J = compOf bank r := by
    rcases (mem_componentsB_iff bank J).1 hJmem with ⟨s, rfl⟩
    exact compOf_eq_of_reach bank ((mem_compOf bank s r).1 hr)
  have hmap_cl : closedB (snocB bank e) (mapCastEmb a J) = true := by
    rw [closedB_iff]
    intro x hx y hxy
    change x ∈ J.map (castEmb a) at hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨j, hj, rfl⟩
    revert hxy
    refine Fin.lastCases ?_ ?_ y
    · intro hxy
      change (snocB bank e (castEmb a j) ∩ snocB bank e (Fin.last a)).Nonempty at hxy
      rw [hbank_cast, hbank_last, he] at hxy
      rcases hxy with ⟨w, hw⟩
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw.2 with rfl | rfl
      · have hj1 : j ∈ compOf bank i₁ :=
          (closedB_iff bank _).1 hJ₁cl i₁ (self_mem_compOf bank i₁) j
            ⟨w, Finset.mem_inter.2 ⟨hu, hw.1⟩⟩
        exact False.elim (Finset.disjoint_left.1 (componentsB_disjoint bank hJmem hJ₁mem hJne1) hj hj1)
      · have hj2 : j ∈ compOf bank i₂ :=
          (closedB_iff bank _).1 hJ₂cl i₂ (self_mem_compOf bank i₂) j
            ⟨w, Finset.mem_inter.2 ⟨hv, hw.1⟩⟩
        exact False.elim (Finset.disjoint_left.1 (componentsB_disjoint bank hJmem hJ₂mem hJne2) hj hj2)
    · intro h hxy
      change (snocB bank e (castEmb a j) ∩ snocB bank e (castEmb a h)).Nonempty at hxy
      rw [hbank_cast, hbank_cast] at hxy
      change castEmb a h ∈ J.map (castEmb a)
      exact Finset.mem_map.2 ⟨h, (closedB_iff bank J).1 hJcl j hj h hxy, rfl⟩
  apply Finset.Subset.antisymm
  · intro x hx
    have hrm : castEmb a r ∈ mapCastEmb a J := Finset.mem_map.2 ⟨r, hr, rfl⟩
    exact closedB_reach hmap_cl hrm ((mem_compOf (snocB bank e) _ x).1 hx)
  · intro x hx
    change x ∈ J.map (castEmb a) at hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨j, hj, rfl⟩
    rw [hJeq] at hj
    exact (mem_compOf (snocB bank e) _ _).2 (snoc_reach_lift bank e ((mem_compOf bank r j).1 hj))

lemma snoc_componentsB {n a : Nat} (bank : Fin a → Finset (Fin n))
    (e : Finset (Fin n)) (u v : Fin n) (he : e = {u, v})
    (i₁ i₂ : Fin a) (hu : u ∈ bank i₁) (hv : v ∈ bank i₂) :
    componentsB (snocB bank e) =
      insert (insert (Fin.last a) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a)))
        ((componentsB bank \ {compOf bank i₁, compOf bank i₂}).map (mapCastEmb a)) ∧
    insert (Fin.last a) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a)) ∉
      (componentsB bank \ {compOf bank i₁, compOf bank i₂}).map (mapCastEmb a) := by
  have hcomp_last := snoc_comp_last bank e u v he i₁ i₂ hu hv
  constructor
  · ext K
    rw [mem_componentsB_iff, Finset.mem_insert, Finset.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      refine Fin.lastCases ?_ ?_ x
      · exact Or.inl hcomp_last
      · intro r
        by_cases hr12 : r ∈ compOf bank i₁ ∪ compOf bank i₂
        · left
          have hmem : castEmb a r ∈ compOf (snocB bank e) (Fin.last a) := by
            rw [hcomp_last]
            exact Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨r, hr12, rfl⟩)
          exact (compOf_eq_of_reach (snocB bank e) ((mem_compOf (snocB bank e) _ _).1 hmem)).symm.trans hcomp_last
        · right
          have hJmem : compOf bank r ∈ componentsB bank := compOf_mem_componentsB bank r
          have hJne1 : compOf bank r ≠ compOf bank i₁ :=
            fun h => hr12 (Finset.mem_union_left _ (h ▸ self_mem_compOf bank r))
          have hJne2 : compOf bank r ≠ compOf bank i₂ :=
            fun h => hr12 (Finset.mem_union_right _ (h ▸ self_mem_compOf bank r))
          have hJdiff : compOf bank r ∈ componentsB bank \ {compOf bank i₁, compOf bank i₂} :=
            Finset.mem_sdiff.2 ⟨hJmem, by simp [hJne1, hJne2]⟩
          exact ⟨compOf bank r, hJdiff,
            (snoc_comp_other bank e u v he i₁ i₂ hu hv hJdiff (self_mem_compOf bank r)).symm⟩
    · rintro (rfl | ⟨J, hJdiff, rfl⟩)
      · exact ⟨Fin.last a, hcomp_last.symm⟩
      · have hJne : J.Nonempty := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hJdiff).1).2.1
        rcases hJne with ⟨r, hr⟩
        exact ⟨castEmb a r, (snoc_comp_other bank e u v he i₁ i₂ hu hv hJdiff hr).symm⟩
  · rw [Finset.mem_map]
    rintro ⟨J, _, hJeq⟩
    have hlast : Fin.last a ∈ insert (Fin.last a) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a)) :=
      Finset.mem_insert_self (Fin.last a) _
    rw [← hJeq] at hlast
    change Fin.last a ∈ J.map (castEmb a) at hlast
    rw [Finset.mem_map] at hlast
    rcases hlast with ⟨j, _, hj⟩
    exact (Fin.castSucc_lt_last j).ne hj

lemma snoc_other_pres {n a : Nat} (bank : Fin a → Finset (Fin n))
    (e : Finset (Fin n)) (u v : Fin n) (he : e = {u, v})
    (i₁ i₂ : Fin a) (hu : u ∈ bank i₁) (hv : v ∈ bank i₂)
    {J : Finset (Fin a)} (hJdiff : J ∈ componentsB bank \ {compOf bank i₁, compOf bank i₂}) :
    (mapCastEmb a J ∈ treesB (snocB bank e) ↔ J ∈ treesB bank) ∧
    widthGCDB (snocB bank e) (mapCastEmb a J) = widthGCDB bank J ∧
    (mapCastEmb a J ∈ badB (snocB bank e) ↔ J ∈ badB bank) ∧
    (mapCastEmb a J ∈ evenBadB (snocB bank e) ↔ J ∈ evenBadB bank) := by
  have hcomps := (snoc_componentsB bank e u v he i₁ i₂ hu hv).1
  have hbank_cast : ∀ j : Fin a, snocB bank e (castEmb a j) = bank j := fun j => snocB_castSucc bank e j
  have hJmem : J ∈ componentsB bank := (Finset.mem_sdiff.1 hJdiff).1
  have hJmem' : mapCastEmb a J ∈ componentsB (snocB bank e) := by
    rw [hcomps]; exact Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨J, hJdiff, rfl⟩)
  have hsupp : supportB (snocB bank e) (mapCastEmb a J) = supportB bank J := by
    ext w
    simp [supportB, mapCastEmb, hbank_cast]
  have hcard : (mapCastEmb a J).card = J.card := Finset.card_map (castEmb a)
  have hsum : (mapCastEmb a J).sum (fun x => (snocB bank e x).card) =
      J.sum (fun x => (bank x).card) := by
    change (J.map (castEmb a)).sum (fun x => (snocB bank e x).card) = _
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl; intro j _; rw [hbank_cast]
  have hgcd : widthGCDB (snocB bank e) (mapCastEmb a J) = widthGCDB bank J := by
    change (J.map (castEmb a)).gcd (fun x => (snocB bank e x).card) = J.gcd (fun x => (bank x).card)
    rw [gcd_map_emb]
    apply Finset.gcd_congr rfl; intro j _; rw [hbank_cast]
  have htree : mapCastEmb a J ∈ treesB (snocB bank e) ↔ J ∈ treesB bank := by
    simp only [treesB, Finset.mem_filter, hJmem', hJmem, true_and, hsum, hcard, hsupp]
  have hbad : mapCastEmb a J ∈ badB (snocB bank e) ↔ J ∈ badB bank := by
    simp only [badB, Finset.mem_filter, htree, hgcd]
  have heven : mapCastEmb a J ∈ evenBadB (snocB bank e) ↔ J ∈ evenBadB bank := by
    simp only [evenBadB, Finset.mem_filter, hbad, hgcd]
  exact ⟨htree, hgcd, hbad, heven⟩

lemma snoc_Jnew_supp {n a : Nat} (bank : Fin a → Finset (Fin n))
    (e : Finset (Fin n)) (u v : Fin n) (he : e = {u, v})
    (i₁ i₂ : Fin a) (hu : u ∈ bank i₁) (hv : v ∈ bank i₂) :
    supportB (snocB bank e)
      (insert (Fin.last a) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a))) =
      supportB bank (compOf bank i₁) ∪ supportB bank (compOf bank i₂) := by
  have hbank_cast : ∀ j : Fin a, snocB bank e (castEmb a j) = bank j := fun j => snocB_castSucc bank e j
  rw [supportB_insert, snocB_last]
  have hmap_supp : supportB (snocB bank e) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a)) =
      supportB bank (compOf bank i₁) ∪ supportB bank (compOf bank i₂) := by
    ext w
    simp only [supportB, Finset.mem_biUnion, Finset.mem_map, Finset.mem_union]
    constructor
    · rintro ⟨_, ⟨j, hj1 | hj2, rfl⟩, hw⟩
      · rw [hbank_cast] at hw; exact Or.inl ⟨j, hj1, hw⟩
      · rw [hbank_cast] at hw; exact Or.inr ⟨j, hj2, hw⟩
    · rintro (⟨j, hj1, hw⟩ | ⟨j, hj2, hw⟩)
      · exact ⟨castEmb a j, ⟨j, Or.inl hj1, rfl⟩, by rwa [hbank_cast]⟩
      · exact ⟨castEmb a j, ⟨j, Or.inr hj2, rfl⟩, by rwa [hbank_cast]⟩
  rw [hmap_supp]
  apply Finset.union_eq_right.2
  rw [he]
  intro w hw
  rw [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i₁, self_mem_compOf bank i₁, hu⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i₂, self_mem_compOf bank i₂, hv⟩)

lemma snoc_Jnew_same {n a : Nat} (bank : Fin a → Finset (Fin n))
    (e : Finset (Fin n)) (u v : Fin n) (huv : u ≠ v) (he : e = {u, v})
    (i₁ i₂ : Fin a) (hu : u ∈ bank i₁) (hv : v ∈ bank i₂)
    (h12 : compOf bank i₁ = compOf bank i₂) :
    let Jnew := insert (Fin.last a) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a))
    Jnew ∉ treesB (snocB bank e) ∧ Jnew ∉ badB (snocB bank e) ∧ Jnew ∉ evenBadB (snocB bank e) := by
  intro Jnew
  have hbank_cast : ∀ j : Fin a, snocB bank e (castEmb a j) = bank j := fun j => snocB_castSucc bank e j
  have hecard : e.card = 2 := by rw [he, Finset.card_pair huv]
  have hlast_not_map : Fin.last a ∉ (compOf bank i₁ ∪ compOf bank i₂).map (castEmb a) := by
    rw [Finset.mem_map]
    rintro ⟨j, _, hj⟩
    exact (Fin.castSucc_lt_last j).ne hj
  have hcard : Jnew.card = (compOf bank i₁).card + 1 := by
    have hJnew_eq : Jnew = insert (Fin.last a) ((compOf bank i₁).map (castEmb a)) := by
      simp only [Jnew, ← h12, Finset.union_idempotent]
    have hnot : Fin.last a ∉ (compOf bank i₁).map (castEmb a) := fun h =>
      hlast_not_map (by rwa [← h12, Finset.union_idempotent])
    rw [hJnew_eq, Finset.card_insert_of_notMem hnot, Finset.card_map]
  have hsum : Jnew.sum (fun x => (snocB bank e x).card) =
      (compOf bank i₁).sum (fun x => (bank x).card) + 2 := by
    rw [Finset.sum_insert hlast_not_map, snocB_last, hecard]
    rw [← h12, Finset.union_idempotent, Finset.sum_map]
    have : (compOf bank i₁).sum (fun j => (snocB bank e (castEmb a j)).card) =
        (compOf bank i₁).sum (fun j => (bank j).card) :=
      Finset.sum_congr rfl (fun j _ => by rw [hbank_cast])
    rw [this]; omega
  have hsupp_eq : supportB (snocB bank e) Jnew = supportB bank (compOf bank i₁) := by
    rw [snoc_Jnew_supp bank e u v he i₁ i₂ hu hv, ← h12, Finset.union_idempotent]
  have hJ₁mem : compOf bank i₁ ∈ componentsB bank := compOf_mem_componentsB bank i₁
  have hle := conn_edge_le bank (component_conn bank hJ₁mem) ⟨i₁, self_mem_compOf bank i₁⟩
  have hnt : Jnew ∉ treesB (snocB bank e) := by
    intro ht
    have heq := (Finset.mem_filter.1 ht).2
    rw [hsum, hcard, hsupp_eq] at heq
    omega
  have hnb : Jnew ∉ badB (snocB bank e) := fun h => hnt (Finset.mem_filter.1 h).1
  have hne' : Jnew ∉ evenBadB (snocB bank e) := fun h => hnb (Finset.mem_filter.1 h).1
  exact ⟨hnt, hnb, hne'⟩

lemma snoc_Jnew_diff {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty)
    (e : Finset (Fin n)) (u v : Fin n) (huv : u ≠ v) (he : e = {u, v})
    (i₁ i₂ : Fin a) (hu : u ∈ bank i₁) (hv : v ∈ bank i₂)
    (h12 : compOf bank i₁ ≠ compOf bank i₂) :
    let Jnew := insert (Fin.last a) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a))
    (Jnew ∈ treesB (snocB bank e) ↔ compOf bank i₁ ∈ treesB bank ∧ compOf bank i₂ ∈ treesB bank) ∧
    widthGCDB (snocB bank e) Jnew =
      Nat.gcd 2 (Nat.gcd (widthGCDB bank (compOf bank i₁)) (widthGCDB bank (compOf bank i₂))) ∧
    (Jnew ∈ badB (snocB bank e) ↔ compOf bank i₁ ∈ evenBadB bank ∧ compOf bank i₂ ∈ evenBadB bank) ∧
    (Jnew ∈ evenBadB (snocB bank e) ↔ compOf bank i₁ ∈ evenBadB bank ∧ compOf bank i₂ ∈ evenBadB bank) := by
  intro Jnew
  have hbank_cast : ∀ j : Fin a, snocB bank e (castEmb a j) = bank j := fun j => snocB_castSucc bank e j
  have hecard : e.card = 2 := by rw [he, Finset.card_pair huv]
  have hJ₁mem : compOf bank i₁ ∈ componentsB bank := compOf_mem_componentsB bank i₁
  have hJ₂mem : compOf bank i₂ ∈ componentsB bank := compOf_mem_componentsB bank i₂
  have hJnew_mem : Jnew ∈ componentsB (snocB bank e) := by
    rw [(snoc_componentsB bank e u v he i₁ i₂ hu hv).1]
    exact Finset.mem_insert_self _ _
  have hlast_not_map : Fin.last a ∉ (compOf bank i₁ ∪ compOf bank i₂).map (castEmb a) := by
    rw [Finset.mem_map]
    rintro ⟨j, _, hj⟩
    exact (Fin.castSucc_lt_last j).ne hj
  have hdisjJ : Disjoint (compOf bank i₁) (compOf bank i₂) :=
    componentsB_disjoint bank hJ₁mem hJ₂mem h12
  have hdisjS : Disjoint (supportB bank (compOf bank i₁)) (supportB bank (compOf bank i₂)) :=
    componentsB_support_disjoint bank hJ₁mem hJ₂mem h12
  have hcard : Jnew.card = (compOf bank i₁).card + (compOf bank i₂).card + 1 := by
    rw [Finset.card_insert_of_notMem hlast_not_map, Finset.card_map,
      Finset.card_union_of_disjoint hdisjJ]
  have hsuppCard : (supportB (snocB bank e) Jnew).card =
      (supportB bank (compOf bank i₁)).card + (supportB bank (compOf bank i₂)).card := by
    rw [snoc_Jnew_supp bank e u v he i₁ i₂ hu hv, Finset.card_union_of_disjoint hdisjS]
  have hsum : Jnew.sum (fun x => (snocB bank e x).card) =
      (compOf bank i₁).sum (fun x => (bank x).card) + (compOf bank i₂).sum (fun x => (bank x).card) + 2 := by
    rw [Finset.sum_insert hlast_not_map, snocB_last, hecard, Finset.sum_map]
    have hcongr : (compOf bank i₁ ∪ compOf bank i₂).sum (fun j => (snocB bank e (castEmb a j)).card) =
        (compOf bank i₁ ∪ compOf bank i₂).sum (fun j => (bank j).card) :=
      Finset.sum_congr rfl (fun j _ => by rw [hbank_cast])
    rw [hcongr, Finset.sum_union hdisjJ]; omega
  have hle1 := conn_edge_le bank (component_conn bank hJ₁mem) ⟨i₁, self_mem_compOf bank i₁⟩
  have hle2 := conn_edge_le bank (component_conn bank hJ₂mem) ⟨i₂, self_mem_compOf bank i₂⟩
  have htree : Jnew ∈ treesB (snocB bank e) ↔
      compOf bank i₁ ∈ treesB bank ∧ compOf bank i₂ ∈ treesB bank := by
    simp only [treesB, Finset.mem_filter, hJnew_mem, hJ₁mem, hJ₂mem, true_and,
      hsum, hcard, hsuppCard]
    omega
  have hgcd : widthGCDB (snocB bank e) Jnew =
      Nat.gcd 2 (Nat.gcd (widthGCDB bank (compOf bank i₁)) (widthGCDB bank (compOf bank i₂))) := by
    change (insert (Fin.last a) ((compOf bank i₁ ∪ compOf bank i₂).map (castEmb a))).gcd
      (fun x => (snocB bank e x).card) = _
    rw [Finset.gcd_insert, snocB_last, hecard, gcd_map_emb]
    have hcongr : (compOf bank i₁ ∪ compOf bank i₂).gcd (fun j => (snocB bank e (castEmb a j)).card) =
        (compOf bank i₁ ∪ compOf bank i₂).gcd (fun j => (bank j).card) :=
      Finset.gcd_congr rfl (fun j _ => by rw [hbank_cast])
    rw [hcongr, Finset.gcd_union]
    rfl
  have hpos1 : 1 ≤ widthGCDB bank (compOf bank i₁) := widthGCDB_pos bank hne ⟨i₁, self_mem_compOf bank i₁⟩
  have hpos2 : 1 ≤ widthGCDB bank (compOf bank i₂) := widthGCDB_pos bank hne ⟨i₂, self_mem_compOf bank i₂⟩
  have hgcd_gt1 : 1 < widthGCDB (snocB bank e) Jnew ↔
      (1 < widthGCDB bank (compOf bank i₁) ∧ widthGCDB bank (compOf bank i₁) % 2 = 0) ∧
      (1 < widthGCDB bank (compOf bank i₂) ∧ widthGCDB bank (compOf bank i₂) % 2 = 0) := by
    rw [hgcd]
    have hdvd2 : Nat.gcd 2 (Nat.gcd (widthGCDB bank (compOf bank i₁)) (widthGCDB bank (compOf bank i₂))) ∣ 2 :=
      Nat.gcd_dvd_left 2 _
    have hle2' : Nat.gcd 2 (Nat.gcd (widthGCDB bank (compOf bank i₁)) (widthGCDB bank (compOf bank i₂))) ≤ 2 :=
      Nat.le_of_dvd (by omega) hdvd2
    constructor
    · intro hgt
      have heq2 : Nat.gcd 2 (Nat.gcd (widthGCDB bank (compOf bank i₁)) (widthGCDB bank (compOf bank i₂))) = 2 := by
        omega
      have h2d : 2 ∣ Nat.gcd (widthGCDB bank (compOf bank i₁)) (widthGCDB bank (compOf bank i₂)) := by
        rw [← heq2]; exact Nat.gcd_dvd_right 2 _
      have h2d1 : 2 ∣ widthGCDB bank (compOf bank i₁) := h2d.trans (Nat.gcd_dvd_left _ _)
      have h2d2 : 2 ∣ widthGCDB bank (compOf bank i₂) := h2d.trans (Nat.gcd_dvd_right _ _)
      have h1ge2 : 2 ≤ widthGCDB bank (compOf bank i₁) := Nat.le_of_dvd (by omega) h2d1
      have h2ge2 : 2 ≤ widthGCDB bank (compOf bank i₂) := Nat.le_of_dvd (by omega) h2d2
      exact ⟨⟨by omega, Nat.mod_eq_zero_of_dvd h2d1⟩, ⟨by omega, Nat.mod_eq_zero_of_dvd h2d2⟩⟩
    · rintro ⟨⟨_, hm1⟩, ⟨_, hm2⟩⟩
      have h2d1 : 2 ∣ widthGCDB bank (compOf bank i₁) := Nat.dvd_of_mod_eq_zero hm1
      have h2d2 : 2 ∣ widthGCDB bank (compOf bank i₂) := Nat.dvd_of_mod_eq_zero hm2
      have h2d : 2 ∣ Nat.gcd 2 (Nat.gcd (widthGCDB bank (compOf bank i₁)) (widthGCDB bank (compOf bank i₂))) :=
        Nat.dvd_gcd (dvd_refl 2) (Nat.dvd_gcd h2d1 h2d2)
      have hpos : 0 < Nat.gcd 2 (Nat.gcd (widthGCDB bank (compOf bank i₁)) (widthGCDB bank (compOf bank i₂))) :=
        Nat.gcd_pos_of_pos_left _ (by omega)
      have hge2 : 2 ≤ Nat.gcd 2 (Nat.gcd (widthGCDB bank (compOf bank i₁)) (widthGCDB bank (compOf bank i₂))) :=
        Nat.le_of_dvd hpos h2d
      omega
  have hbad : Jnew ∈ badB (snocB bank e) ↔
      compOf bank i₁ ∈ evenBadB bank ∧ compOf bank i₂ ∈ evenBadB bank := by
    simp only [badB, evenBadB, Finset.mem_filter, htree, hgcd_gt1]
    tauto
  have heven : Jnew ∈ evenBadB (snocB bank e) ↔
      compOf bank i₁ ∈ evenBadB bank ∧ compOf bank i₂ ∈ evenBadB bank := by
    rw [evenBadB, Finset.mem_filter, hbad]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      have hgt : 1 < widthGCDB (snocB bank e) Jnew := (Finset.mem_filter.1 (hbad.2 h)).2
      have hdvd2 : widthGCDB (snocB bank e) Jnew ∣ 2 := by rw [hgcd]; exact Nat.gcd_dvd_left 2 _
      have hle2' : widthGCDB (snocB bank e) Jnew ≤ 2 := Nat.le_of_dvd (by omega) hdvd2
      omega
  exact ⟨htree, hgcd, hbad, heven⟩

lemma snoc_comp_analysis {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) (_hcov : ∀ j : Fin n, ∃ i : Fin a, j ∈ bank i)
    (e : Finset (Fin n)) (u v : Fin n) (huv : u ≠ v) (he : e = {u, v})
    (i₁ i₂ : Fin a) (hu : u ∈ bank i₁) (hv : v ∈ bank i₂) :
    let bank' := snocB bank e
    let J₁ := compOf bank i₁
    let J₂ := compOf bank i₂
    let Jnew := insert (Fin.last a) ((J₁ ∪ J₂).map (castEmb a))
    componentsB bank' =
      insert Jnew ((componentsB bank \ {J₁, J₂}).map (mapCastEmb a)) ∧
    Jnew ∉ (componentsB bank \ {J₁, J₂}).map (mapCastEmb a) ∧
    (∀ J ∈ componentsB bank \ {J₁, J₂},
      (mapCastEmb a J ∈ treesB bank' ↔ J ∈ treesB bank) ∧
      widthGCDB bank' (mapCastEmb a J) = widthGCDB bank J ∧
      (mapCastEmb a J ∈ badB bank' ↔ J ∈ badB bank) ∧
      (mapCastEmb a J ∈ evenBadB bank' ↔ J ∈ evenBadB bank)) ∧
    (J₁ = J₂ → Jnew ∉ treesB bank' ∧ Jnew ∉ badB bank' ∧ Jnew ∉ evenBadB bank') ∧
    (J₁ ≠ J₂ →
      (Jnew ∈ treesB bank' ↔ J₁ ∈ treesB bank ∧ J₂ ∈ treesB bank) ∧
      widthGCDB bank' Jnew = Nat.gcd 2 (Nat.gcd (widthGCDB bank J₁) (widthGCDB bank J₂)) ∧
      (Jnew ∈ badB bank' ↔ J₁ ∈ evenBadB bank ∧ J₂ ∈ evenBadB bank) ∧
      (Jnew ∈ evenBadB bank' ↔ J₁ ∈ evenBadB bank ∧ J₂ ∈ evenBadB bank)) := by
  have h12 := snoc_componentsB bank e u v he i₁ i₂ hu hv
  exact ⟨h12.1, h12.2,
    fun J hJ => snoc_other_pres bank e u v he i₁ i₂ hu hv hJ,
    fun h => snoc_Jnew_same bank e u v huv he i₁ i₂ hu hv h,
    fun h => snoc_Jnew_diff bank hne e u v huv he i₁ i₂ hu hv h⟩

lemma snoc_bad_evenBad_cards {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) (hcov : ∀ j : Fin n, ∃ i : Fin a, j ∈ bank i)
    (e : Finset (Fin n)) (he : e.card = 2) :
    (badB bank).card ≤ (badB (snocB bank e)).card + 2 ∧
    (evenBadB bank).card ≤ (evenBadB (snocB bank e)).card + 1 := by
  classical
  rcases Finset.card_eq_two.1 he with ⟨u, v, huv, heuv⟩
  rcases hcov u with ⟨i₁, hu⟩
  rcases hcov v with ⟨i₂, hv⟩
  let bank' := snocB bank e
  let J₁ := compOf bank i₁
  let J₂ := compOf bank i₂
  let Jnew := insert (Fin.last a) ((J₁ ∪ J₂).map (castEmb a))
  rcases snoc_comp_analysis bank hne hcov e u v huv heuv i₁ i₂ hu hv with
    ⟨hcomps, hJnew_not_in, hother, hsame, hdiff⟩
  -- Bad/evenBad subsets of untouched components embed into badB bank' / evenBadB bank'
  have hbad_sub : ((badB bank) \ {J₁, J₂}).map (mapCastEmb a) ⊆ badB bank' := by
    intro K hK
    rw [Finset.mem_map] at hK
    rcases hK with ⟨J, hJ, rfl⟩
    rw [Finset.mem_sdiff] at hJ
    have hJcomp : J ∈ componentsB bank := (Finset.mem_filter.1 (Finset.mem_filter.1 hJ.1).1).1
    have hJdiff : J ∈ componentsB bank \ {J₁, J₂} := Finset.mem_sdiff.2 ⟨hJcomp, hJ.2⟩
    exact (hother J hJdiff).2.2.1.2 hJ.1
  have hbad_card : (badB bank).card ≤ (badB bank').card + 2 := by
    have h1 := Finset.card_le_card hbad_sub
    rw [Finset.card_map] at h1
    have h2 : (badB bank).card ≤ ((badB bank) \ {J₁, J₂}).card + ({J₁, J₂} : Finset _).card := by
      have := Finset.card_le_card (subset_sdiff_union_aux (badB bank) {J₁, J₂})
      have := Finset.card_union_le ((badB bank) \ {J₁, J₂}) {J₁, J₂}
      omega
    have h3 : ({J₁, J₂} : Finset (Finset (Fin a))).card ≤ 2 := Finset.card_le_two
    omega
  have heven_sub : ((evenBadB bank) \ {J₁, J₂}).map (mapCastEmb a) ⊆ evenBadB bank' := by
    intro K hK
    rw [Finset.mem_map] at hK
    rcases hK with ⟨J, hJ, rfl⟩
    rw [Finset.mem_sdiff] at hJ
    have hJcomp : J ∈ componentsB bank :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hJ.1).1).1).1
    have hJdiff : J ∈ componentsB bank \ {J₁, J₂} := Finset.mem_sdiff.2 ⟨hJcomp, hJ.2⟩
    exact (hother J hJdiff).2.2.2.2 hJ.1
  have hJnew_not_ev : Jnew ∉ ((evenBadB bank) \ {J₁, J₂}).map (mapCastEmb a) := by
    intro h
    apply hJnew_not_in
    rw [Finset.mem_map] at h ⊢
    rcases h with ⟨J, hJ, hEq⟩
    rw [Finset.mem_sdiff] at hJ
    have hJcomp : J ∈ componentsB bank :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hJ.1).1).1).1
    exact ⟨J, Finset.mem_sdiff.2 ⟨hJcomp, hJ.2⟩, hEq⟩
  have heven_card : (evenBadB bank).card ≤ (evenBadB bank').card + 1 := by
    by_cases h12 : J₁ = J₂
    · have h1 := Finset.card_le_card heven_sub
      rw [Finset.card_map] at h1
      have hpair : ({J₁, J₂} : Finset (Finset (Fin a))) = {J₁} := by simp [h12]
      rw [hpair] at h1
      have h2 : (evenBadB bank).card ≤ ((evenBadB bank) \ {J₁}).card + 1 := by
        have hA := Finset.card_le_card (subset_sdiff_union_aux (evenBadB bank) {J₁})
        have hB := Finset.card_union_le ((evenBadB bank) \ {J₁}) {J₁}
        have hC : ({J₁} : Finset (Finset (Fin a))).card = 1 := Finset.card_singleton J₁
        omega
      omega
    · by_cases hboth : J₁ ∈ evenBadB bank ∧ J₂ ∈ evenBadB bank
      · have hJnew_ev : Jnew ∈ evenBadB bank' := (hdiff h12).2.2.2.2 hboth
        have hsub' : insert Jnew (((evenBadB bank) \ {J₁, J₂}).map (mapCastEmb a)) ⊆ evenBadB bank' :=
          Finset.insert_subset hJnew_ev heven_sub
        have h1 := Finset.card_le_card hsub'
        rw [Finset.card_insert_of_notMem hJnew_not_ev, Finset.card_map] at h1
        have h2 : (evenBadB bank).card ≤ ((evenBadB bank) \ {J₁, J₂}).card + 2 := by
          have := Finset.card_le_card (subset_sdiff_union_aux (evenBadB bank) {J₁, J₂})
          have := Finset.card_union_le ((evenBadB bank) \ {J₁, J₂}) {J₁, J₂}
          have h3 : ({J₁, J₂} : Finset (Finset (Fin a))).card ≤ 2 := Finset.card_le_two
          omega
        omega
      · have h1 := Finset.card_le_card heven_sub
        rw [Finset.card_map] at h1
        have hinter_le : (evenBadB bank ∩ {J₁, J₂}).card ≤ 1 := by
          by_cases h1e : J₁ ∈ evenBadB bank
          · have h2e : J₂ ∉ evenBadB bank := fun h => hboth ⟨h1e, h⟩
            have heq : evenBadB bank ∩ {J₁, J₂} = {J₁} := by
              ext J; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨hJ, rfl | rfl⟩
                · rfl
                · exact False.elim (h2e hJ)
              · rintro rfl; exact ⟨h1e, Or.inl rfl⟩
            rw [heq]; simp
          · have hsub : evenBadB bank ∩ {J₁, J₂} ⊆ {J₂} := by
              intro J hJ
              rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hJ
              rcases hJ.2 with rfl | rfl
              · exact False.elim (h1e hJ.1)
              · exact Finset.mem_singleton_self J₂
            exact (Finset.card_le_card hsub).trans (by simp)
        have hsplit := Finset.card_sdiff_add_card_inter (evenBadB bank) {J₁, J₂}
        omega
  exact ⟨hbad_card, heven_card⟩

-- ============================================================================
-- Section 7: Final Equivalence (Lower Bound and Upper Bound)
-- ============================================================================

lemma addCasesB_left {n t s : Nat} (scope : Fin t → Finset (Fin n))
    (extra : Fin s → Finset (Fin n)) (i : Fin t) :
    addCasesB scope extra (Fin.castAdd s i) = scope i := by
  simp [addCasesB, Fin.addCases_left]

lemma addCasesB_right {n t s : Nat} (scope : Fin t → Finset (Fin n))
    (extra : Fin s → Finset (Fin n)) (j : Fin s) :
    addCasesB scope extra (Fin.natAdd t j) = extra j := by
  simp [addCasesB, Fin.addCases_right]

lemma addCases_zero {n t : Nat} (scope : Fin t → Finset (Fin n))
    (extra : Fin 0 → Finset (Fin n)) :
    addCasesB scope extra = scope := by
  funext i
  simpa using addCasesB_left scope extra i

lemma addCases_snoc {n t s : Nat} (scope : Fin t → Finset (Fin n))
    (extra : Fin (s + 1) → Finset (Fin n)) :
    addCasesB scope extra =
      snocB (addCasesB scope (fun j : Fin s => extra j.castSucc)) (extra (Fin.last s)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · change addCasesB scope extra (Fin.last (t + s)) =
      snocB (addCasesB scope (fun j : Fin s => extra j.castSucc)) (extra (Fin.last s)) (Fin.last (t + s))
    rw [snocB_last]
    have hlast : Fin.last (t + s) = Fin.natAdd t (Fin.last s) := by
      ext; simp [Fin.last, Fin.natAdd]
    rw [hlast, addCasesB_right]
  · intro j
    change addCasesB scope extra j.castSucc =
      snocB (addCasesB scope (fun j : Fin s => extra j.castSucc)) (extra (Fin.last s)) j.castSucc
    rw [snocB_castSucc]
    have hjlt : j.val < t + s := j.isLt
    by_cases hlt : j.val < t
    · have hj : j = Fin.castAdd s ⟨j.val, hlt⟩ := by ext; simp
      have h1 : j.castSucc = Fin.castAdd (s + 1) ⟨j.val, hlt⟩ := by ext; simp
      conv_lhs => rw [h1]
      conv_rhs => rw [hj]
      rw [addCasesB_left, addCasesB_left]
    · have hsub : j.val - t < s := by omega
      have hj : j = Fin.natAdd t ⟨j.val - t, hsub⟩ := by ext; simp; omega
      have h1 : j.castSucc = Fin.natAdd t (Fin.castSucc ⟨j.val - t, hsub⟩) := by ext; simp; omega
      conv_lhs => rw [h1]
      conv_rhs => rw [hj]
      rw [addCasesB_right, addCasesB_right]

lemma lower_bound_ind {n t : Nat} (scope : Fin t → Finset (Fin n))
    (hne : ∀ i, (scope i).Nonempty) (hcov : ∀ j : Fin n, ∃ i : Fin t, j ∈ scope i) :
    ∀ (s : Nat) (extra : Fin s → Finset (Fin n)), (∀ i, (extra i).card = 2) →
      (badB scope).card ≤ (badB (addCasesB scope extra)).card + 2 * s ∧
      (evenBadB scope).card ≤ (evenBadB (addCasesB scope extra)).card + s := by
  intro s
  induction s with
  | zero =>
    intro extra _
    rw [addCases_zero]; omega
  | succ s ih =>
    intro extra hex
    let extra' : Fin s → Finset (Fin n) := fun j => extra j.castSucc
    have hex' : ∀ j, (extra' j).card = 2 := fun j => hex j.castSucc
    have hprev := ih extra' hex'
    let bank' := addCasesB scope extra'
    have hne' : ∀ i, (bank' i).Nonempty := by
      intro i
      by_cases hlt : i.val < t
      · have hi : i = Fin.castAdd s ⟨i.val, hlt⟩ := by ext; simp
        rw [hi]; dsimp only [bank']; rw [addCasesB_left]; exact hne _
      · have hsub : i.val - t < s := by omega
        have hi : i = Fin.natAdd t ⟨i.val - t, hsub⟩ := by ext; simp; omega
        rw [hi]; dsimp only [bank']; rw [addCasesB_right]
        exact Finset.card_pos.1 (by rw [hex']; omega)
    have hcov' : ∀ j : Fin n, ∃ i, j ∈ bank' i := by
      intro j
      rcases hcov j with ⟨i, hi⟩
      exact ⟨Fin.castAdd s i, by dsimp only [bank']; rw [addCasesB_left]; exact hi⟩
    have hstep := snoc_bad_evenBad_cards bank' hne' hcov' (extra (Fin.last s)) (hex (Fin.last s))
    dsimp only [bank', extra'] at hstep hprev
    rw [addCases_snoc scope extra]
    omega

lemma canRecoverB_equiv {n a b : Nat} (σ : Fin a ≃ Fin b)
    (bank₁ : Fin a → Finset (Fin n)) (bank₂ : Fin b → Finset (Fin n))
    (h : ∀ i, bank₁ i = bank₂ (σ i)) :
    canRecoverB a bank₁ ↔ canRecoverB b bank₂ := by
  have dir : ∀ {a b : Nat} (σ : Fin a ≃ Fin b)
      (bank₁ : Fin a → Finset (Fin n)) (bank₂ : Fin b → Finset (Fin n)),
      (∀ i, bank₁ i = bank₂ (σ i)) → canRecoverB b bank₂ → canRecoverB a bank₁ := by
    intro a b σ bank₁ bank₂ hbank hrec z
    rcases hrec z with ⟨c₂, hc₂⟩
    let φ : (Fin a → Finset (Fin n)) ≃ (Fin b → Finset (Fin n)) :=
      Equiv.arrowCongr σ (Equiv.refl _)
    refine ⟨fun p => c₂ (φ p), fun x => ?_⟩
    rw [← hc₂ x]
    refine Finset.sum_equiv φ ?_ (fun _ _ => rfl)
    intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hsub, hne⟩
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := hsub (σ.symm j)
        rw [hbank (σ.symm j), σ.apply_symm_apply] at this
        simpa [φ] using this
      · have := hne (σ.symm j)
        rw [hbank (σ.symm j), σ.apply_symm_apply] at this
        simpa [φ] using this
    · rintro ⟨hsub, hne⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := hsub (σ i)
        rw [← hbank i] at this
        simpa [φ] using this
      · have := hne (σ i)
        rw [← hbank i] at this
        simpa [φ] using this
  exact ⟨dir σ.symm bank₂ bank₁ (fun j => by rw [h (σ.symm j), σ.apply_symm_apply]),
    dir σ bank₁ bank₂ h⟩

-- Exact card updates for our 3 greedy repair moves
lemma snoc_repair_pair_odd {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) (hcov : ∀ j : Fin n, ∃ i : Fin a, j ∈ bank i)
    {J₁ J₂ : Finset (Fin a)} (h1 : J₁ ∈ badB bank) (h2 : J₂ ∈ badB bank) (h12 : J₁ ≠ J₂)
    (hnotboth : ¬ (J₁ ∈ evenBadB bank ∧ J₂ ∈ evenBadB bank)) :
    ∃ e : Finset (Fin n), e.card = 2 ∧
      (badB (snocB bank e)).card + 2 = (badB bank).card ∧
      (evenBadB (snocB bank e)).card +
        (if J₁ ∈ evenBadB bank then 1 else 0) + (if J₂ ∈ evenBadB bank then 1 else 0) =
        (evenBadB bank).card := by
  classical
  have h1comp : J₁ ∈ componentsB bank := (Finset.mem_filter.1 (Finset.mem_filter.1 h1).1).1
  have h2comp : J₂ ∈ componentsB bank := (Finset.mem_filter.1 (Finset.mem_filter.1 h2).1).1
  rcases (mem_componentsB_iff bank J₁).1 h1comp with ⟨i₁, hJ₁eq⟩
  rcases (mem_componentsB_iff bank J₂).1 h2comp with ⟨i₂, hJ₂eq⟩
  rcases hne i₁ with ⟨u, hu⟩
  rcases hne i₂ with ⟨v, hv⟩
  have huv : u ≠ v := by
    intro heq
    subst heq
    have h1' : u ∈ supportB bank J₁ := Finset.mem_biUnion.2 ⟨i₁, hJ₁eq ▸ self_mem_compOf bank i₁, hu⟩
    have h2' : u ∈ supportB bank J₂ := Finset.mem_biUnion.2 ⟨i₂, hJ₂eq ▸ self_mem_compOf bank i₂, hv⟩
    exact Finset.disjoint_left.1 (componentsB_support_disjoint bank h1comp h2comp h12) h1' h2'
  let e : Finset (Fin n) := {u, v}
  have hecard : e.card = 2 := Finset.card_pair huv
  let bank' := snocB bank e
  rcases snoc_comp_analysis bank hne hcov e u v huv rfl i₁ i₂ hu hv with
    ⟨hcomps, hJnew_not_in, hother, _, hdiff⟩
  rw [← hJ₁eq, ← hJ₂eq] at hcomps hJnew_not_in hother hdiff
  let Jnew := insert (Fin.last a) ((J₁ ∪ J₂).map (castEmb a))
  have hJnew_nb : Jnew ∉ badB bank' := fun h => hnotboth ((hdiff h12).2.2.1.1 h)
  have hJnew_ne : Jnew ∉ evenBadB bank' := fun h => hnotboth ((hdiff h12).2.2.2.1 h)
  have hbad_eq : badB bank' = ((badB bank) \ {J₁, J₂}).map (mapCastEmb a) := by
    ext K
    constructor
    · intro hK
      have hKcomp : K ∈ componentsB bank' := (Finset.mem_filter.1 (Finset.mem_filter.1 hK).1).1
      rw [hcomps, Finset.mem_insert] at hKcomp
      rcases hKcomp with rfl | hKmap
      · exact False.elim (hJnew_nb hK)
      · rw [Finset.mem_map] at hKmap ⊢
        rcases hKmap with ⟨J, hJdiff, rfl⟩
        exact ⟨J, Finset.mem_sdiff.2 ⟨(hother J hJdiff).2.2.1.1 hK, (Finset.mem_sdiff.1 hJdiff).2⟩, rfl⟩
    · intro hK
      rw [Finset.mem_map] at hK
      rcases hK with ⟨J, hJ, rfl⟩
      rw [Finset.mem_sdiff] at hJ
      have hJcomp : J ∈ componentsB bank := (Finset.mem_filter.1 (Finset.mem_filter.1 hJ.1).1).1
      exact (hother J (Finset.mem_sdiff.2 ⟨hJcomp, hJ.2⟩)).2.2.1.2 hJ.1
  have heven_eq : evenBadB bank' = ((evenBadB bank) \ {J₁, J₂}).map (mapCastEmb a) := by
    ext K
    constructor
    · intro hK
      have hKcomp : K ∈ componentsB bank' :=
        (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hK).1).1).1
      rw [hcomps, Finset.mem_insert] at hKcomp
      rcases hKcomp with rfl | hKmap
      · exact False.elim (hJnew_ne hK)
      · rw [Finset.mem_map] at hKmap ⊢
        rcases hKmap with ⟨J, hJdiff, rfl⟩
        exact ⟨J, Finset.mem_sdiff.2 ⟨(hother J hJdiff).2.2.2.1 hK, (Finset.mem_sdiff.1 hJdiff).2⟩, rfl⟩
    · intro hK
      rw [Finset.mem_map] at hK
      rcases hK with ⟨J, hJ, rfl⟩
      rw [Finset.mem_sdiff] at hJ
      have hJcomp : J ∈ componentsB bank :=
        (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hJ.1).1).1).1
      exact (hother J (Finset.mem_sdiff.2 ⟨hJcomp, hJ.2⟩)).2.2.2.2 hJ.1
  refine ⟨e, hecard, ?_, ?_⟩
  · rw [hbad_eq, Finset.card_map]
    have hsub : ({J₁, J₂} : Finset (Finset (Fin a))) ⊆ badB bank :=
      Finset.insert_subset h1 (Finset.singleton_subset_iff.2 h2)
    have hsplit := Finset.card_sdiff_add_card_eq_card hsub
    rw [Finset.card_pair h12] at hsplit
    exact hsplit
  · rw [heven_eq, Finset.card_map]
    have hsplit := Finset.card_sdiff_add_card_inter (evenBadB bank) {J₁, J₂}
    have hinter : (evenBadB bank ∩ {J₁, J₂}).card =
        (if J₁ ∈ evenBadB bank then 1 else 0) + (if J₂ ∈ evenBadB bank then 1 else 0) := by
      by_cases he1 : J₁ ∈ evenBadB bank <;> by_cases he2 : J₂ ∈ evenBadB bank
      · exact False.elim (hnotboth ⟨he1, he2⟩)
      · have : evenBadB bank ∩ {J₁, J₂} = {J₁} := by
          ext J; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hJ, rfl | rfl⟩
            · rfl
            · exact False.elim (he2 hJ)
          · rintro rfl; exact ⟨he1, Or.inl rfl⟩
        rw [this]; simp [he1, he2]
      · have : evenBadB bank ∩ {J₁, J₂} = {J₂} := by
          ext J; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hJ, rfl | rfl⟩
            · exact False.elim (he1 hJ)
            · rfl
          · rintro rfl; exact ⟨he2, Or.inr rfl⟩
        rw [this]; simp [he1, he2]
      · have : evenBadB bank ∩ {J₁, J₂} = ∅ := by
          ext J; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
            Finset.notMem_empty, iff_false, not_and]
          rintro hJ (rfl | rfl)
          · exact he1 hJ
          · exact he2 hJ
        rw [this]; simp [he1, he2]
    omega

lemma snoc_repair_single {n a : Nat} (bank : Fin a → Finset (Fin n))
    (hne : ∀ i, (bank i).Nonempty) (hcov : ∀ j : Fin n, ∃ i : Fin a, j ∈ bank i)
    {J₁ : Finset (Fin a)} (h1 : J₁ ∈ badB bank) :
    ∃ e : Finset (Fin n), e.card = 2 ∧
      (badB (snocB bank e)).card + 1 = (badB bank).card ∧
      (evenBadB (snocB bank e)).card + (if J₁ ∈ evenBadB bank then 1 else 0) =
        (evenBadB bank).card := by
  classical
  have h1tree : J₁ ∈ treesB bank := (Finset.mem_filter.1 h1).1
  have h1gcd : 1 < widthGCDB bank J₁ := (Finset.mem_filter.1 h1).2
  have h1comp : J₁ ∈ componentsB bank := (Finset.mem_filter.1 h1tree).1
  rcases (mem_componentsB_iff bank J₁).1 h1comp with ⟨i₁, hJ₁eq⟩
  have hi₁mem : i₁ ∈ J₁ := hJ₁eq ▸ self_mem_compOf bank i₁
  have h2le : 2 ≤ (bank i₁).card := by
    have hdvd : widthGCDB bank J₁ ∣ (bank i₁).card := Finset.gcd_dvd hi₁mem
    have hpos : 0 < (bank i₁).card := Finset.card_pos.2 (hne i₁)
    have := Nat.le_of_dvd hpos hdvd
    omega
  rcases Finset.one_lt_card.1 (by omega : 1 < (bank i₁).card) with ⟨u, hu, v, hv, huv⟩
  let e : Finset (Fin n) := {u, v}
  have hecard : e.card = 2 := Finset.card_pair huv
  let bank' := snocB bank e
  rcases snoc_comp_analysis bank hne hcov e u v huv rfl i₁ i₁ hu hv with
    ⟨hcomps, hJnew_not_in, hother, hsame, _⟩
  rw [← hJ₁eq] at hcomps hJnew_not_in hother hsame
  let Jnew := insert (Fin.last a) ((J₁ ∪ J₁).map (castEmb a))
  have hJnew_nb : Jnew ∉ badB bank' := (hsame rfl).2.1
  have hJnew_ne : Jnew ∉ evenBadB bank' := (hsame rfl).2.2
  have hpair : ({J₁, J₁} : Finset (Finset (Fin a))) = {J₁} := by simp
  rw [hpair] at hcomps hJnew_not_in hother
  have hbad_eq : badB bank' = ((badB bank) \ {J₁}).map (mapCastEmb a) := by
    ext K
    constructor
    · intro hK
      have hKcomp : K ∈ componentsB bank' := (Finset.mem_filter.1 (Finset.mem_filter.1 hK).1).1
      rw [hcomps, Finset.mem_insert] at hKcomp
      rcases hKcomp with rfl | hKmap
      · exact False.elim (hJnew_nb hK)
      · rw [Finset.mem_map] at hKmap ⊢
        rcases hKmap with ⟨J, hJdiff, rfl⟩
        exact ⟨J, Finset.mem_sdiff.2 ⟨(hother J hJdiff).2.2.1.1 hK, (Finset.mem_sdiff.1 hJdiff).2⟩, rfl⟩
    · intro hK
      rw [Finset.mem_map] at hK
      rcases hK with ⟨J, hJ, rfl⟩
      rw [Finset.mem_sdiff] at hJ
      have hJcomp : J ∈ componentsB bank := (Finset.mem_filter.1 (Finset.mem_filter.1 hJ.1).1).1
      exact (hother J (Finset.mem_sdiff.2 ⟨hJcomp, hJ.2⟩)).2.2.1.2 hJ.1
  have heven_eq : evenBadB bank' = ((evenBadB bank) \ {J₁}).map (mapCastEmb a) := by
    ext K
    constructor
    · intro hK
      have hKcomp : K ∈ componentsB bank' :=
        (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hK).1).1).1
      rw [hcomps, Finset.mem_insert] at hKcomp
      rcases hKcomp with rfl | hKmap
      · exact False.elim (hJnew_ne hK)
      · rw [Finset.mem_map] at hKmap ⊢
        rcases hKmap with ⟨J, hJdiff, rfl⟩
        exact ⟨J, Finset.mem_sdiff.2 ⟨(hother J hJdiff).2.2.2.1 hK, (Finset.mem_sdiff.1 hJdiff).2⟩, rfl⟩
    · intro hK
      rw [Finset.mem_map] at hK
      rcases hK with ⟨J, hJ, rfl⟩
      rw [Finset.mem_sdiff] at hJ
      have hJcomp : J ∈ componentsB bank :=
        (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hJ.1).1).1).1
      exact (hother J (Finset.mem_sdiff.2 ⟨hJcomp, hJ.2⟩)).2.2.2.2 hJ.1
  refine ⟨e, hecard, ?_, ?_⟩
  · rw [hbad_eq, Finset.card_map]
    have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.2 h1)
    simpa using hsplit
  · rw [heven_eq, Finset.card_map]
    by_cases he1 : J₁ ∈ evenBadB bank
    · have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.2 he1)
      simpa [he1] using hsplit
    · have hsdiff : evenBadB bank \ {J₁} = evenBadB bank := by
        ext J; simp only [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨fun h => h.1, fun h => ⟨h, fun heq => he1 (heq ▸ h)⟩⟩
      simp [he1, hsdiff]

lemma upper_bound_ind {n : Nat} :
    ∀ (m a : Nat) (bank : Fin a → Finset (Fin n)),
      (∀ i, (bank i).Nonempty) → (∀ j : Fin n, ∃ i : Fin a, j ∈ bank i) →
      max (evenBadB bank).card (((badB bank).card + 1) / 2) ≤ m →
      ∃ (s : Nat) (extra : Fin s → Finset (Fin n)), s ≤ m ∧
        (∀ i, (extra i).card = 2) ∧ canRecoverB (a + s) (addCasesB bank extra) := by
  classical
  intro m
  induction m with
  | zero =>
    intro a bank hne hcov hmu
    have hbad0 : (badB bank).card = 0 := by omega
    have hbad_empty : badB bank = ∅ := Finset.card_eq_zero.1 hbad0
    refine ⟨0, Fin.elim0, le_refl 0, fun i => Fin.elim0 i, ?_⟩
    rw [addCases_zero]
    exact badB_empty_imp_canRecoverB bank hne hcov hbad_empty
  | succ m ih =>
    intro a bank hne hcov hmu
    by_cases hbad_empty : badB bank = ∅
    · refine ⟨0, Fin.elim0, Nat.zero_le _, fun i => Fin.elim0 i, ?_⟩
      rw [addCases_zero]
      exact badB_empty_imp_canRecoverB bank hne hcov hbad_empty
    · let oddBad := badB bank \ evenBadB bank
      have heven_sub : evenBadB bank ⊆ badB bank := Finset.filter_subset _ _
      have hcard_split : oddBad.card + (evenBadB bank).card = (badB bank).card :=
        Finset.card_sdiff_add_card_eq_card heven_sub
      -- Helper to lift a single-step repair e with μ(snoc bank e) ≤ m
      have lift_step : ∀ e : Finset (Fin n), e.card = 2 →
          max (evenBadB (snocB bank e)).card (((badB (snocB bank e)).card + 1) / 2) ≤ m →
          ∃ (s : Nat) (extra : Fin s → Finset (Fin n)), s ≤ m + 1 ∧
            (∀ i, (extra i).card = 2) ∧ canRecoverB (a + s) (addCasesB bank extra) := by
        intro e he hmu'
        let bank' := snocB bank e
        have hne' : ∀ i, (bank' i).Nonempty := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · dsimp only [bank']; rw [snocB_last]; exact Finset.card_pos.1 (by omega)
          · intro j; dsimp only [bank']; rw [snocB_castSucc]; exact hne j
        have hcov' : ∀ j : Fin n, ∃ i, j ∈ bank' i := by
          intro j
          rcases hcov j with ⟨i, hi⟩
          exact ⟨i.castSucc, by dsimp only [bank']; rw [snocB_castSucc]; exact hi⟩
        rcases ih (a + 1) bank' hne' hcov' hmu' with ⟨s', extra', hs', hex', hrec'⟩
        let extra : Fin (s' + 1) → Finset (Fin n) := consB e extra'
        have hex : ∀ i, (extra i).card = 2 := by
          intro i
          refine Fin.cases ?_ ?_ i
          · simpa [extra, consB] using he
          · intro j; simpa [extra, consB] using hex' j
        have hrec : canRecoverB (a + (s' + 1)) (addCasesB bank extra) := by
          have heq : a + (s' + 1) = (a + 1) + s' := by omega
          let σ : Fin (a + (s' + 1)) ≃ Fin ((a + 1) + s') := finCongr heq
          refine (canRecoverB_equiv σ (addCasesB bank extra) (addCasesB bank' extra') ?_).2 hrec'
          intro i
          by_cases h1 : i.val < a
          · have hl : i = Fin.castAdd (s' + 1) ⟨i.val, h1⟩ := by ext; simp
            have hr : σ i = Fin.castAdd s' (Fin.castSucc ⟨i.val, h1⟩) := by ext; simp [σ]
            conv_lhs => rw [hl]
            rw [hr, addCasesB_left, addCasesB_left]; exact (snocB_castSucc bank e _).symm
          · by_cases h2 : i.val = a
            · have hl : i = Fin.natAdd a (0 : Fin (s' + 1)) := by ext; simp [h2]
              have hr : σ i = Fin.castAdd s' (Fin.last a) := by ext; simp [σ, h2]
              conv_lhs => rw [hl]
              rw [hr, addCasesB_right, addCasesB_left]
              dsimp only [bank', extra, consB]
              rw [snocB_last, Fin.cons_zero]
            · have hlt1 : i.val - (a + 1) < s' := by omega
              have hl : i = Fin.natAdd a (Fin.succ ⟨i.val - (a + 1), hlt1⟩) := by
                ext; simp; omega
              have hr : σ i = Fin.natAdd (a + 1) ⟨i.val - (a + 1), hlt1⟩ := by
                ext; simp [σ]; omega
              conv_lhs => rw [hl]
              rw [hr, addCasesB_right, addCasesB_right]
              dsimp only [extra, consB]
              rw [Fin.cons_succ]
        exact ⟨s' + 1, extra, by omega, hex, hrec⟩
      -- Choose greedy repair move
      by_cases hEO : (evenBadB bank).Nonempty ∧ oddBad.Nonempty
      · rcases hEO.1 with ⟨J₁, hJ₁e⟩
        rcases hEO.2 with ⟨J₂, hJ₂o⟩
        have hJ₁b : J₁ ∈ badB bank := heven_sub hJ₁e
        have hJ₂b : J₂ ∈ badB bank := (Finset.mem_sdiff.1 hJ₂o).1
        have hJ₂ne : J₂ ∉ evenBadB bank := (Finset.mem_sdiff.1 hJ₂o).2
        have h12 : J₁ ≠ J₂ := fun h => hJ₂ne (h ▸ hJ₁e)
        have hnb : ¬ (J₁ ∈ evenBadB bank ∧ J₂ ∈ evenBadB bank) := fun h => hJ₂ne h.2
        rcases snoc_repair_pair_odd bank hne hcov hJ₁b hJ₂b h12 hnb with ⟨e, he, hbc, hec⟩
        simp only [hJ₁e, hJ₂ne, ↓reduceIte] at hec
        exact lift_step e he (by omega)
      · by_cases hO2 : 2 ≤ oddBad.card
        · rcases Finset.one_lt_card.1 (by omega : 1 < oddBad.card) with ⟨J₁, hJ₁o, J₂, hJ₂o, h12⟩
          have hJ₁b : J₁ ∈ badB bank := (Finset.mem_sdiff.1 hJ₁o).1
          have hJ₂b : J₂ ∈ badB bank := (Finset.mem_sdiff.1 hJ₂o).1
          have hJ₁ne : J₁ ∉ evenBadB bank := (Finset.mem_sdiff.1 hJ₁o).2
          have hJ₂ne : J₂ ∉ evenBadB bank := (Finset.mem_sdiff.1 hJ₂o).2
          have hnb : ¬ (J₁ ∈ evenBadB bank ∧ J₂ ∈ evenBadB bank) := fun h => hJ₁ne h.1
          rcases snoc_repair_pair_odd bank hne hcov hJ₁b hJ₂b h12 hnb with ⟨e, he, hbc, hec⟩
          simp only [hJ₁ne, hJ₂ne, ↓reduceIte] at hec
          have he0 : (evenBadB bank).card = 0 := by
            by_contra hne0
            have hene : (evenBadB bank).Nonempty := Finset.card_pos.1 (by omega)
            have hone : oddBad.Nonempty := Finset.card_pos.1 (by omega)
            exact hEO ⟨hene, hone⟩
          exact lift_step e he (by omega)
        · have hbad_ne : (badB bank).Nonempty := Finset.nonempty_iff_ne_empty.2 hbad_empty
          rcases hbad_ne with ⟨J₁, hJ₁b⟩
          rcases snoc_repair_single bank hne hcov hJ₁b with ⟨e, he, hbc, hec⟩
          by_cases hO0 : oddBad.card = 0
          · have hJ₁e : J₁ ∈ evenBadB bank := by
              by_contra hne1
              have : J₁ ∈ oddBad := Finset.mem_sdiff.2 ⟨hJ₁b, hne1⟩
              have := Finset.card_pos.2 ⟨J₁, this⟩
              omega
            simp only [hJ₁e, ↓reduceIte] at hec
            exact lift_step e he (by omega)
          · have hO1 : oddBad.card = 1 := by omega
            have hE0 : (evenBadB bank).card = 0 := by
              by_contra hne0
              exact hEO ⟨Finset.card_pos.1 (by omega), Finset.card_pos.1 (by omega)⟩
            have hJ₁ne : J₁ ∉ evenBadB bank := by
              intro h; have := Finset.card_pos.2 ⟨J₁, h⟩; omega
            simp only [hJ₁ne, ↓reduceIte] at hec
            exact lift_step e he (by omega)

theorem main :
    ∀ (n t : Nat) (scope : Fin t → Finset (Fin n)),
  (∀ i, (scope i).Nonempty) → (∀ j : Fin n, ∃ i, j ∈ scope i) →
  let Bits := Finset (Fin n)
  let sites := (Finset.univ : Finset (Fin n))
  let rows := (Finset.univ : Finset (Fin t))
  let closed := fun (J : Finset (Fin t)) => J.toList.all (fun i => rows.toList.all
    (fun h => !(decide (scope i ∩ scope h).Nonempty) || decide (h ∈ J)))
  let components := rows.powerset.filter (fun J => J.Nonempty ∧ closed J = true ∧
    ∀ K ∈ J.powerset, K.Nonempty → closed K = true → K = J)
  let support := fun (J : Finset (Fin t)) => J.biUnion scope
  let trees := components.filter (fun J =>
    J.sum (fun i => (scope i).card) + 1 = J.card + (support J).card)
  let widthGCD := fun (J : Finset (Fin t)) => J.gcd (fun i => (scope i).card)
  let bad := trees.filter (fun J => 1 < widthGCD J)
  let evenBad := bad.filter (fun J => widthGCD J % 2 = 0)
  let canRecover := fun (a : Nat) (bank : Fin a → Bits) =>
    let patterns := (Finset.univ : Finset (Fin a → Bits)).filter
      (fun p => ∀ i, p i ⊆ bank i)
    ∀ z : Bits, ∃ c : (Fin a → Bits) → Int, ∀ x : Bits,
      (patterns.filter (fun p => ∀ i, x ∩ bank i ≠ p i)).sum c =
        (if x = z then (1 : Int) else 0)
  ∀ k : Nat,
    (∃ (s : Nat) (extra : Fin s → Bits), s ≤ k ∧ (∀ i, (extra i).card = 2) ∧
      canRecover (t + s) (Fin.addCases scope extra)) ↔
      max evenBad.card ((bad.card + 1) / 2) ≤ k := by
  intro n t scope hne hcov Bits sites rows closed components support trees widthGCD bad evenBad
    canRecover k
  have hclosed : closed = closedB scope := rfl
  have hcomp : components = componentsB scope := by
    ext J
    simp only [components, componentsB, rows, Finset.mem_filter, Finset.mem_powerset, hclosed]
  have htrees : trees = treesB scope := by
    ext J
    conv_lhs => dsimp only [trees]; rw [Finset.mem_filter]
    conv_rhs => dsimp only [treesB]; rw [Finset.mem_filter]
    rw [hcomp]
    rfl
  have hbad : bad = badB scope := by
    ext J
    conv_lhs => dsimp only [bad]; rw [Finset.mem_filter]
    conv_rhs => dsimp only [badB]; rw [Finset.mem_filter]
    rw [htrees]
    rfl
  have hevenBad : evenBad = evenBadB scope := by
    ext J
    conv_lhs => dsimp only [evenBad]; rw [Finset.mem_filter]
    conv_rhs => dsimp only [evenBadB]; rw [Finset.mem_filter]
    rw [hbad]
    rfl
  have hrec_iff : ∀ (a : Nat) (bank : Fin a → Finset (Fin n)),
      canRecover a bank ↔ canRecoverB a bank := by
    intro a bank
    constructor
    · intro h z; rcases h z with ⟨c, hc⟩; exact ⟨c, fun x => by convert hc x⟩
    · intro h z; rcases h z with ⟨c, hc⟩; exact ⟨c, fun x => by convert hc x⟩
  rw [hbad, hevenBad]
  constructor
  · rintro ⟨s, extra, hsk, hex, hrec⟩
    have hrec' : canRecoverB (t + s) (addCasesB scope extra) := (hrec_iff (t + s) _).1 hrec
    have hne' : ∀ i, (addCasesB scope extra i).Nonempty := by
      intro i
      by_cases hlt : i.val < t
      · have hi : i = Fin.castAdd s ⟨i.val, hlt⟩ := by ext; simp
        rw [hi, addCasesB_left]; exact hne _
      · have hsub : i.val - t < s := by omega
        have hi : i = Fin.natAdd t ⟨i.val - t, hsub⟩ := by ext; simp; omega
        rw [hi, addCasesB_right]; exact Finset.card_pos.1 (by rw [hex]; omega)
    have hbad0 : badB (addCasesB scope extra) = ∅ :=
      canRecoverB_imp_badB_empty (addCasesB scope extra) hne' hrec'
    have hev0 : evenBadB (addCasesB scope extra) = ∅ := by
      rw [evenBadB, hbad0]; simp
    have hlb := lower_bound_ind scope hne hcov s extra hex
    rw [hbad0, hev0] at hlb
    simp at hlb
    omega
  · intro hk
    rcases upper_bound_ind k t scope hne hcov hk with ⟨s, extra, hsk, hex, hrec⟩
    exact ⟨s, extra, hsk, hex, (hrec_iff (t + s) _).2 hrec⟩

end PEqualNP.Outside.L_lib_1147

theorem PEqualNP.Outside.L_lib_1147 :
    ∀ (n t : Nat) (scope : Fin t → Finset (Fin n)),
  (∀ i, (scope i).Nonempty) → (∀ j : Fin n, ∃ i, j ∈ scope i) →
  let Bits := Finset (Fin n)
  let sites := (Finset.univ : Finset (Fin n))
  let rows := (Finset.univ : Finset (Fin t))
  let closed := fun (J : Finset (Fin t)) => J.toList.all (fun i => rows.toList.all
    (fun h => !(decide (scope i ∩ scope h).Nonempty) || decide (h ∈ J)))
  let components := rows.powerset.filter (fun J => J.Nonempty ∧ closed J = true ∧
    ∀ K ∈ J.powerset, K.Nonempty → closed K = true → K = J)
  let support := fun (J : Finset (Fin t)) => J.biUnion scope
  let trees := components.filter (fun J =>
    J.sum (fun i => (scope i).card) + 1 = J.card + (support J).card)
  let widthGCD := fun (J : Finset (Fin t)) => J.gcd (fun i => (scope i).card)
  let bad := trees.filter (fun J => 1 < widthGCD J)
  let evenBad := bad.filter (fun J => widthGCD J % 2 = 0)
  let canRecover := fun (a : Nat) (bank : Fin a → Bits) =>
    let patterns := (Finset.univ : Finset (Fin a → Bits)).filter
      (fun p => ∀ i, p i ⊆ bank i)
    ∀ z : Bits, ∃ c : (Fin a → Bits) → Int, ∀ x : Bits,
      (patterns.filter (fun p => ∀ i, x ∩ bank i ≠ p i)).sum c =
        (if x = z then (1 : Int) else 0)
  ∀ k : Nat,
    (∃ (s : Nat) (extra : Fin s → Bits), s ≤ k ∧ (∀ i, (extra i).card = 2) ∧
      canRecover (t + s) (Fin.addCases scope extra)) ↔
      max evenBad.card ((bad.card + 1) / 2) ≤ k :=
  PEqualNP.Outside.L_lib_1147.main
