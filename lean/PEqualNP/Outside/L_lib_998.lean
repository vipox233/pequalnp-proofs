import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_998
open Finset Relation
section G
variable {V : Type*} [Fintype V] [DecidableEq V]
def Conn (r : V → V → Prop) (S : Finset V) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ r x y) i j
def IsCon (r : V → V → Prop) (A B S : Finset V) : Prop :=
  (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty ∧ Conn r S
def IsPack (r : V → V → Prop) (A B : Finset V) (F : Finset (Finset V)) : Prop :=
  (∀ S ∈ F, IsCon r A B S) ∧ ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T
def IsSep (r : V → V → Prop) (A B C : Finset V) : Prop :=
  ∀ S, IsCon r A B S → (S ∩ C).Nonempty
def Av (r : V → V → Prop) (X : Finset V) (s t : V) : Prop := s ∉ X ∧ t ∉ X ∧ r s t
theorem rtg_ne {R R' : V → V → Prop} (h : ∀ a b, R a b → a ≠ b → R' a b) {i j : V}
    (hij : ReflTransGen R i j) : ReflTransGen R' i j := by
  induction hij with
  | refl => exact ReflTransGen.refl
  | @tail b c _ hbc ih =>
    by_cases hne : b = c
    · rw [← hne]; exact ih
    · exact ih.tail (h _ _ hbc hne)
theorem rtg_symm {R : V → V → Prop} (hR : ∀ a b, R a b → R b a) {a b : V}
    (h : ReflTransGen R a b) : ReflTransGen R b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (hR _ _ hbc) ih
theorem rtg_map {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop} (f : α → β)
    (h : ∀ a b, R a b → R' (f a) (f b)) {a b : α} (hab : ReflTransGen R a b) :
    ReflTransGen R' (f a) (f b) := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)
theorem conn_mono {r r' : V → V → Prop} {S T : Finset V} (hc : Conn r S) (hST : S ⊆ T)
    (h : ∀ p ∈ S, ∀ q ∈ S, r p q → p ≠ q → r' p q) : ∀ i ∈ S, ∀ j ∈ S,
    ReflTransGen (fun x y => x ∈ T ∧ y ∈ T ∧ r' x y) i j := by
  intro i hi j hj
  exact rtg_ne (fun a b hab hne => ⟨hST hab.1, hST hab.2.1, h a hab.1 b hab.2.1 hab.2.2 hne⟩)
    (hc i hi j hj)
theorem conn_of {r r' : V → V → Prop} {S : Finset V} (hc : Conn r S)
    (h : ∀ p ∈ S, ∀ q ∈ S, r p q → p ≠ q → r' p q) : Conn r' S :=
  conn_mono hc (subset_refl S) h
theorem conn_union {r : V → V → Prop} {S T : Finset V} (hS : Conn r S) (hT : Conn r T)
    (hST : (S ∩ T).Nonempty) : Conn r (S ∪ T) := by
  obtain ⟨z, hz⟩ := hST
  rw [mem_inter] at hz
  have h1 := conn_mono (T := S ∪ T) (r' := r) hS subset_union_left (fun p _ q _ h _ => h)
  have h2 := conn_mono (T := S ∪ T) (r' := r) hT subset_union_right (fun p _ q _ h _ => h)
  intro i hi j hj
  rcases mem_union.mp hi with hi | hi <;> rcases mem_union.mp hj with hj | hj
  · exact h1 i hi j hj
  · exact (h1 i hi z hz.1).trans (h2 z hz.2 j hj)
  · exact (h2 i hi z hz.2).trans (h1 z hz.1 j hj)
  · exact h2 i hi j hj
theorem conn_in {r : V → V → Prop} {P : V → Prop} (hP : ∀ p q, r p q → P q) {S : Finset V}
    (hc : Conn r S) {z : V} (hz : z ∈ S) (hPz : P z) : ∀ p ∈ S, P p := by
  intro p hp
  rcases (hc z hz p hp).cases_tail with h | ⟨q, _, hq⟩
  · rw [h]; exact hPz
  · exact hP _ _ hq.2.2
theorem rtg_avoid {r : V → V → Prop} {X : Finset V} {a p : V} (h : ReflTransGen (Av r X) a p)
    (ha : a ∉ X) : p ∉ X := by
  induction h with
  | refl => exact ha
  | tail _ hst _ => exact hst.2.1
theorem av_src {r : V → V → Prop} {X : Finset V} {a p : V} (h : ReflTransGen (Av r X) a p)
    (hp : p ∉ X) : a ∉ X := by
  rcases h.cases_head with h | ⟨c, hc, _⟩
  · rw [h]; exact hp
  · exact hc.1
theorem comp_sep {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {A B X : Finset V}
    (hX : IsSep r A B X) {a b p : V} (ha : a ∈ A) (haX : a ∉ X) (hb : b ∈ B)
    (hap : ReflTransGen (Av r X) a p) (hbp : ReflTransGen (Av r X) b p) : False := by
  classical
  have hRs : ∀ s t, Av r X s t → Av r X t s := fun s t h => ⟨h.2.1, h.1, hr _ _ h.2.2⟩
  let K := univ.filter (fun q => ReflTransGen (Av r X) a q)
  have hK : ∀ q, q ∈ K ↔ ReflTransGen (Av r X) a q := fun q => by simp [K]
  have hab : ReflTransGen (Av r X) a b := hap.trans (rtg_symm hRs hbp)
  have key : ∀ q1 q2, ReflTransGen (Av r X) a q1 → ReflTransGen (Av r X) q1 q2 →
      ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ r x y) q1 q2 := by
    intro q1 q2 h1 h12
    induction h12 with
    | refl => exact ReflTransGen.refl
    | @tail b' c' h1b hbc ih =>
      have hb' : ReflTransGen (Av r X) a b' := h1.trans h1b
      exact ih.tail ⟨(hK _).2 hb', (hK _).2 (hb'.tail hbc), hbc.2.2⟩
  have hcon : IsCon r A B K := by
    refine ⟨⟨a, mem_inter.2 ⟨(hK _).2 ReflTransGen.refl, ha⟩⟩,
      ⟨b, mem_inter.2 ⟨(hK _).2 hab, hb⟩⟩, ?_⟩
    intro i hi j hj
    rw [hK] at hi hj
    exact key i j hi ((rtg_symm hRs hi).trans hj)
  obtain ⟨q, hq⟩ := hX K hcon
  rw [mem_inter, hK] at hq
  exact rtg_avoid hq.1 haX hq.2
theorem first_hit {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {T X : Finset V} {s z : V}
    (h : ReflTransGen (fun x y => x ∈ T ∧ y ∈ T ∧ r x y) s z) (hs : s ∈ T) (hz : z ∈ X) :
    ∃ T' ⊆ T, s ∈ T' ∧ (∃ z', T' ∩ X = {z'}) ∧ Conn r T' ∧
      ∀ p ∈ T', p ∉ X → ReflTransGen (Av r X) s p := by
  have single : ∀ a, a ∈ T → a ∈ X → ∃ T' ⊆ T, a ∈ T' ∧ (∃ z', T' ∩ X = {z'}) ∧ Conn r T' ∧
      ∀ p ∈ T', p ∉ X → ReflTransGen (Av r X) a p := by
    intro a haT haX
    refine ⟨{a}, singleton_subset_iff.2 haT, mem_singleton_self a, ⟨a, ?_⟩, ?_, ?_⟩
    · rw [singleton_inter_of_mem haX]
    · intro i hi j hj
      rw [mem_singleton] at hi hj
      rw [hi, hj]
    · intro p hp hpX
      rw [mem_singleton] at hp
      rw [hp] at hpX
      exact absurd haX hpX
  induction h using ReflTransGen.head_induction_on with
  | refl => exact single _ hs hz
  | head hab hbz ih =>
    rename_i a b
    obtain ⟨T'', hT'', hbT'', ⟨z', hz'⟩, hc, hreach⟩ := ih hab.2.1
    by_cases haX : a ∈ X
    · exact single a hab.1 haX
    · refine ⟨insert a T'', insert_subset hab.1 hT'', mem_insert_self _ _, ⟨z', ?_⟩, ?_, ?_⟩
      · rw [insert_inter_of_notMem haX]; exact hz'
      · intro i hi j hj
        have hc' := conn_mono hc (subset_insert a T'') (fun p _ q _ h _ => h)
        have hab' : ReflTransGen (fun x y => x ∈ insert a T'' ∧ y ∈ insert a T'' ∧ r x y) a b :=
          ReflTransGen.single ⟨mem_insert_self _ _, mem_insert_of_mem hbT'', hab.2.2⟩
        have hba' : ReflTransGen (fun x y => x ∈ insert a T'' ∧ y ∈ insert a T'' ∧ r x y) b a :=
          ReflTransGen.single ⟨mem_insert_of_mem hbT'', mem_insert_self _ _, hr _ _ hab.2.2⟩
        rcases mem_insert.1 hi with hi | hi <;> rcases mem_insert.1 hj with hj | hj
        · rw [hi, hj]
        · rw [hi]; exact hab'.trans (hc' b hbT'' j hj)
        · rw [hj]; exact (hc' i hi b hbT'').trans hba'
        · exact hc' i hi j hj
      · intro p hp hpX
        rcases mem_insert.1 hp with hp | hp
        · rw [hp]
        · have h1 := hreach p hp hpX
          have hbX : b ∉ X := av_src h1 hpX
          exact ReflTransGen.head ⟨haX, hbX, hab.2.2⟩ h1
theorem menger_base (r : V → V → Prop) (h0 : ∀ a b, r a b → a = b) (A B : Finset V) :
    ∃ C, IsSep r A B C ∧ ∃ F, IsPack r A B F ∧ C.card ≤ F.card := by
  have key : ∀ (S : Finset V) i j, ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ r x y) i j →
      i = j := by
    intro S i j h
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (h0 _ _ hbc.2.2)
  refine ⟨A ∩ B, ?_, (A ∩ B).image (fun a => {a}), ⟨?_, ?_⟩, ?_⟩
  · intro S ⟨⟨i, hi⟩, ⟨j, hj⟩, hc⟩
    rw [mem_inter] at hi hj
    have := key S i j (hc i hi.1 j hj.1)
    rw [← this] at hj
    exact ⟨i, mem_inter.2 ⟨hi.1, mem_inter.2 ⟨hi.2, hj.2⟩⟩⟩
  · intro S hS
    rw [mem_image] at hS
    obtain ⟨a, ha, rfl⟩ := hS
    rw [mem_inter] at ha
    refine ⟨⟨a, by simp [ha.1]⟩, ⟨a, by simp [ha.2]⟩, ?_⟩
    intro i hi j hj
    rw [mem_singleton] at hi hj
    rw [hi, hj]
  · intro S hS T hT hne
    rw [mem_image] at hS hT
    obtain ⟨a, _, rfl⟩ := hS
    obtain ⟨b, _, rfl⟩ := hT
    rw [disjoint_singleton]
    intro hab; exact hne (by rw [hab])
  · rw [card_image_of_injective _ singleton_injective]
def fc (x y z : V) : V := if z = y then x else z
def rc (r : V → V → Prop) (x y : V) (p q : V) : Prop :=
  ∃ p0 q0, fc x y p0 = p ∧ fc x y q0 = q ∧ r p0 q0
def pre (x y : V) (S : Finset V) : Finset V := univ.filter (fun z => fc x y z ∈ S)
theorem mem_pre {x y z : V} {S : Finset V} : z ∈ pre x y S ↔ fc x y z ∈ S := by
  simp [pre]
theorem fc_ne {x y : V} (hxy : x ≠ y) (z : V) : fc x y z ≠ y := by
  unfold fc
  split_ifs with h
  · exact hxy
  · exact h
theorem fc_of_ne {x y z : V} (h : z ≠ y) : fc x y z = z := by
  unfold fc; rw [if_neg h]
theorem fc_y (x y : V) : fc x y y = x := by
  unfold fc; rw [if_pos rfl]
theorem fc_fiber {x y p q : V} (h : fc x y p = fc x y q) (hne : p ≠ q) :
    (p = x ∧ q = y) ∨ (p = y ∧ q = x) := by
  by_cases hp : p = y <;> by_cases hq : q = y
  · exact absurd (hp.trans hq.symm) hne
  · rw [hp, fc_y, fc_of_ne hq] at h
    exact Or.inr ⟨hp, h.symm⟩
  · rw [hq, fc_y, fc_of_ne hp] at h
    exact Or.inl ⟨h, hq⟩
  · rw [fc_of_ne hp, fc_of_ne hq] at h
    exact absurd h hne
theorem fiber_rtg {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {x y : V} (hrxy : r x y)
    {W : Finset V} {p q : V} (h : fc x y p = fc x y q) (hp : p ∈ W) (hq : q ∈ W) :
    ReflTransGen (fun a b => a ∈ W ∧ b ∈ W ∧ r a b) p q := by
  by_cases hne : p = q
  · rw [hne]
  · rcases fc_fiber h hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      exact ReflTransGen.single ⟨hp, hq, hrxy⟩
    · subst h1; subst h2
      exact ReflTransGen.single ⟨hp, hq, hr _ _ hrxy⟩
theorem proj_con {r : V → V → Prop} {x y : V} {A B T : Finset V} (hT : IsCon r A B T) :
    IsCon (rc r x y) (A.image (fc x y)) (B.image (fc x y)) (T.image (fc x y)) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hc⟩ := hT
  rw [mem_inter] at ha hb
  refine ⟨⟨fc x y a, mem_inter.2 ⟨mem_image_of_mem _ ha.1, mem_image_of_mem _ ha.2⟩⟩,
    ⟨fc x y b, mem_inter.2 ⟨mem_image_of_mem _ hb.1, mem_image_of_mem _ hb.2⟩⟩, ?_⟩
  intro i hi j hj
  obtain ⟨i0, hi0, rfl⟩ := mem_image.1 hi
  obtain ⟨j0, hj0, rfl⟩ := mem_image.1 hj
  exact rtg_map (fc x y) (fun s t hst => ⟨mem_image_of_mem _ hst.1,
    mem_image_of_mem _ hst.2.1, s, t, rfl, rfl, hst.2.2⟩) (hc i0 hi0 j0 hj0)
theorem y_not_mem {r : V → V → Prop} {x y : V} (hxy : x ≠ y) {A B S : Finset V}
    (hS : IsCon (rc r x y) (A.image (fc x y)) B S) : y ∉ S := by
  intro hyS
  obtain ⟨⟨s, hs⟩, _, hc⟩ := hS
  rw [mem_inter, mem_image] at hs
  obtain ⟨hsS, a, _, rfl⟩ := hs
  rcases (hc _ hsS y hyS).cases_tail with h | ⟨q, _, hq⟩
  · exact fc_ne hxy a h.symm
  · obtain ⟨p0, q0, _, h2, _⟩ := hq.2.2
    exact fc_ne hxy q0 h2
theorem lift_con {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {x y : V} (hrxy : r x y)
    {A B S : Finset V} (hS : IsCon (rc r x y) (A.image (fc x y)) (B.image (fc x y)) S) :
    IsCon r A B (pre x y S) := by
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩, hc⟩ := hS
  rw [mem_inter, mem_image] at hs ht
  obtain ⟨hsS, a, ha, rfl⟩ := hs
  obtain ⟨htS, b, hb, rfl⟩ := ht
  refine ⟨⟨a, mem_inter.2 ⟨mem_pre.2 hsS, ha⟩⟩, ⟨b, mem_inter.2 ⟨mem_pre.2 htS, hb⟩⟩, ?_⟩
  intro i hi j hj
  have key : ∀ t, ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ rc r x y a b) (fc x y i) t →
      ∀ j, fc x y j = t → j ∈ pre x y S →
      ReflTransGen (fun a b => a ∈ pre x y S ∧ b ∈ pre x y S ∧ r a b) i j := by
    intro t ht
    induction ht with
    | refl => intro j hj hjp; exact fiber_rtg hr hrxy hj.symm hi hjp
    | tail _ hst ih =>
      intro j hj hjp
      obtain ⟨p0, q0, h1, h2, h3⟩ := hst.2.2
      have hp0 : p0 ∈ pre x y S := mem_pre.2 (h1 ▸ hst.1)
      have hq0 : q0 ∈ pre x y S := mem_pre.2 (h2 ▸ hst.2.1)
      exact ((ih p0 h1 hp0).tail ⟨hp0, hq0, h3⟩).trans
        (fiber_rtg hr hrxy (h2.trans hj.symm) hq0 hjp)
  exact key _ (hc _ (mem_pre.1 hi) _ (mem_pre.1 hj)) j rfl hj
theorem pull_sep {r : V → V → Prop} {x y : V} {A B C1 : Finset V}
    (h : IsSep (rc r x y) (A.image (fc x y)) (B.image (fc x y)) C1) :
    IsSep r A B (pre x y C1) := by
  intro T hT
  obtain ⟨c, hc⟩ := h _ (proj_con hT)
  rw [mem_inter, mem_image] at hc
  obtain ⟨⟨t, ht, rfl⟩, hc⟩ := hc
  exact ⟨t, mem_inter.2 ⟨ht, mem_pre.2 hc⟩⟩
theorem lift_pack {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {x y : V} (hxy : x ≠ y)
    (hrxy : r x y) {A B : Finset V} {F1 : Finset (Finset V)}
    (hF : IsPack (rc r x y) (A.image (fc x y)) (B.image (fc x y)) F1) :
    IsPack r A B (F1.image (pre x y)) ∧ (F1.image (pre x y)).card = F1.card := by
  have hinj : Set.InjOn (pre x y) F1 := by
    intro S hS T hT h
    have hyS := y_not_mem hxy (hF.1 S hS)
    have hyT := y_not_mem hxy (hF.1 T hT)
    ext z
    constructor
    · intro hz
      have hzy : z ≠ y := fun h => hyS (h ▸ hz)
      have : z ∈ pre x y S := mem_pre.2 (by rw [fc_of_ne hzy]; exact hz)
      rw [h, mem_pre, fc_of_ne hzy] at this
      exact this
    · intro hz
      have hzy : z ≠ y := fun h => hyT (h ▸ hz)
      have : z ∈ pre x y T := mem_pre.2 (by rw [fc_of_ne hzy]; exact hz)
      rw [← h, mem_pre, fc_of_ne hzy] at this
      exact this
  refine ⟨⟨?_, ?_⟩, card_image_of_injOn hinj⟩
  · intro S hS
    obtain ⟨S0, hS0, rfl⟩ := mem_image.1 hS
    exact lift_con hr hrxy (hF.1 S0 hS0)
  · intro S hS T hT hST
    obtain ⟨S0, hS0, rfl⟩ := mem_image.1 hS
    obtain ⟨T0, hT0, rfl⟩ := mem_image.1 hT
    have hne : S0 ≠ T0 := fun h => hST (by rw [h])
    have hd := hF.2 S0 hS0 T0 hT0 hne
    rw [Finset.disjoint_left] at hd ⊢
    intro z hz hz'
    exact hd (mem_pre.1 hz) (mem_pre.1 hz')
theorem contr_step {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {x y : V} (hxy : x ≠ y)
    (hrxy : r x y) {A B C1 : Finset V}
    (hC1 : IsSep (rc r x y) (A.image (fc x y)) (B.image (fc x y)) C1)
    {F1 : Finset (Finset V)} (hF1 : IsPack (rc r x y) (A.image (fc x y)) (B.image (fc x y)) F1)
    (hCF : C1.card ≤ F1.card) :
    ∃ X F, IsSep r A B X ∧ IsPack r A B F ∧ X.card ≤ F.card + 1 ∧
      (X.card ≤ F.card ∨ (x ∈ X ∧ y ∈ X)) := by
  obtain ⟨hP, hcard⟩ := lift_pack hr hxy hrxy hF1
  refine ⟨pre x y C1, F1.image (pre x y), pull_sep hC1, hP, ?_, ?_⟩
  · rw [hcard]
    have hsub : pre x y C1 ⊆ insert y C1 := by
      intro z hz
      rw [mem_pre] at hz
      by_cases hzy : z = y
      · rw [hzy]; exact mem_insert_self _ _
      · rw [fc_of_ne hzy] at hz; exact mem_insert_of_mem hz
    have := card_le_card hsub
    have := card_insert_le y C1
    omega
  · by_cases hx : x ∈ C1
    · right
      exact ⟨mem_pre.2 (by rw [fc_of_ne hxy]; exact hx), mem_pre.2 (by rw [fc_y]; exact hx)⟩
    · left
      rw [hcard]
      refine le_trans (card_le_card ?_) hCF
      intro z hz
      rw [mem_pre] at hz
      by_cases hzy : z = y
      · rw [hzy, fc_y] at hz; exact absurd hz hx
      · rwa [fc_of_ne hzy] at hz
theorem cover {X : Finset V} {F : Finset (Finset V)}
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T)
    (hmeet : ∀ S ∈ F, (S ∩ X).Nonempty) (hc : X.card ≤ F.card) :
    (∀ z ∈ X, ∃ S ∈ F, z ∈ S) ∧ ∀ S ∈ F, ∀ z ∈ S, ∀ z' ∈ S, z ∈ X → z' ∈ X → z = z' := by
  have h1 : (F.biUnion (fun S => S ∩ X)).card = ∑ S ∈ F, (S ∩ X).card :=
    card_biUnion (fun S hS T hT h =>
      Disjoint.mono inter_subset_left inter_subset_left (hdis S hS T hT h))
  have h2 : F.biUnion (fun S => S ∩ X) ⊆ X := biUnion_subset.2 (fun S _ => inter_subset_right)
  have hle : ∀ S ∈ F, 1 ≤ (S ∩ X).card := fun S hS => Nat.succ_le_of_lt (card_pos.2 (hmeet S hS))
  have h3 : ∑ S ∈ F, 1 ≤ ∑ S ∈ F, (S ∩ X).card := sum_le_sum hle
  have h4 : ∑ S ∈ F, (S ∩ X).card ≤ ∑ S ∈ F, 1 := by
    rw [← h1]; simp only [sum_const, smul_eq_mul, mul_one]; exact (card_le_card h2).trans hc
  have h5 : ∀ S ∈ F, 1 = (S ∩ X).card := (sum_eq_sum_iff_of_le hle).1 (le_antisymm h3 h4)
  have h6 : F.biUnion (fun S => S ∩ X) = X := by
    apply eq_of_subset_of_card_le h2
    rw [h1]
    simp only [sum_const, smul_eq_mul, mul_one] at h3
    omega
  constructor
  · intro z hz
    rw [← h6, mem_biUnion] at hz
    obtain ⟨S, hS, hzS⟩ := hz
    exact ⟨S, hS, (mem_inter.1 hzS).1⟩
  · intro S hS z hz z' hz' hzX hz'X
    have := h5 S hS
    rw [eq_comm, card_eq_one] at this
    obtain ⟨a, ha⟩ := this
    have e1 : z ∈ S ∩ X := mem_inter.2 ⟨hz, hzX⟩
    have e2 : z' ∈ S ∩ X := mem_inter.2 ⟨hz', hz'X⟩
    rw [ha, mem_singleton] at e1 e2
    rw [e1, e2]
theorem comb {r rA rB : V → V → Prop} {A B X : Finset V} {FA FB : Finset (Finset V)}
    (hA : IsPack rA A X FA) (hB : IsPack rB X B FB) (hcA : X.card ≤ FA.card)
    (hcB : X.card ≤ FB.card) (hrA : ∀ p q, rA p q → r p q) (hrB : ∀ p q, rB p q → r p q)
    (hside : ∀ S ∈ FA, ∀ T ∈ FB, ∀ p ∈ S, p ∈ T → p ∈ X) :
    ∃ F, IsPack r A B F ∧ X.card ≤ F.card := by
  obtain ⟨cA1, cA2⟩ := cover hA.2 (fun S hS => (hA.1 S hS).2.1) hcA
  obtain ⟨cB1, cB2⟩ := cover hB.2 (fun S hS => (hB.1 S hS).1) hcB
  choose! σA hσA using cA1
  choose! σB hσB using cB1
  refine ⟨X.image (fun z => σA z ∪ σB z), ⟨?_, ?_⟩, ?_⟩
  · intro S hS
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hS
    obtain ⟨hA1, hA2⟩ := hσA z hz
    obtain ⟨hB1, hB2⟩ := hσB z hz
    obtain ⟨⟨a, ha⟩, _, hcA'⟩ := hA.1 _ hA1
    obtain ⟨_, ⟨b, hb⟩, hcB'⟩ := hB.1 _ hB1
    refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩, conn_union (conn_of hcA' (fun p _ q _ h _ => hrA p q h))
      (conn_of hcB' (fun p _ q _ h _ => hrB p q h)) ⟨z, mem_inter.2 ⟨hA2, hB2⟩⟩⟩
    · rw [mem_inter] at ha ⊢; exact ⟨mem_union_left _ ha.1, ha.2⟩
    · rw [mem_inter] at hb ⊢; exact ⟨mem_union_right _ hb.1, hb.2⟩
  · intro S hS T hT hST
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hS
    obtain ⟨z', hz', rfl⟩ := mem_image.1 hT
    have hzz' : z ≠ z' := fun h => hST (by rw [h])
    rw [Finset.disjoint_left]
    intro p hp hp'
    rcases mem_union.1 hp with hp | hp <;> rcases mem_union.1 hp' with hp' | hp'
    · by_cases he : σA z = σA z'
      · exact hzz' (cA2 _ (hσA z hz).1 z (hσA z hz).2 z' (he ▸ (hσA z' hz').2) hz hz')
      · exact Finset.disjoint_left.1 (hA.2 _ (hσA z hz).1 _ (hσA z' hz').1 he) hp hp'
    · have hpX := hside _ (hσA z hz).1 _ (hσB z' hz').1 p hp hp'
      have e1 := cA2 _ (hσA z hz).1 p hp z (hσA z hz).2 hpX hz
      have e2 := cB2 _ (hσB z' hz').1 p hp' z' (hσB z' hz').2 hpX hz'
      exact hzz' (e1.symm.trans e2)
    · have hpX := hside _ (hσA z' hz').1 _ (hσB z hz).1 p hp' hp
      have e1 := cA2 _ (hσA z' hz').1 p hp' z' (hσA z' hz').2 hpX hz'
      have e2 := cB2 _ (hσB z hz).1 p hp z (hσB z hz).2 hpX hz
      exact hzz' (e2.symm.trans e1)
    · by_cases he : σB z = σB z'
      · exact hzz' (cB2 _ (hσB z hz).1 z (hσB z hz).2 z' (he ▸ (hσB z' hz').2) hz hz')
      · exact Finset.disjoint_left.1 (hB.2 _ (hσB z hz).1 _ (hσB z' hz').1 he) hp hp'
  · rw [card_image_of_injOn]
    intro z hz z' hz' h
    have : z ∈ σA z' ∪ σB z' := by
      have h0 : z ∈ σA z ∪ σB z := mem_union_left _ (hσA z hz).2
      simp only at h
      rw [h] at h0
      exact h0
    rcases mem_union.1 this with h1 | h1
    · exact cA2 _ (hσA z' hz').1 z h1 z' (hσA z' hz').2 hz hz'
    · exact cB2 _ (hσB z' hz').1 z h1 z' (hσB z' hz').2 hz hz'
open Classical in
noncomputable def nl (r : V → V → Prop) : ℕ :=
  (univ.filter (fun p : V × V => p.1 ≠ p.2 ∧ r p.1 p.2)).card
theorem nl_lt {r r' : V → V → Prop} (h : ∀ p q, r' p q → r p q) {x y : V} (hxy : x ≠ y)
    (hr : r x y) (hr' : ¬ r' x y) : nl r' < nl r := by
  classical
  unfold nl
  apply card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(x, y), ?_, ?_⟩
    · simp [hxy, hr]
    · simp [hr']
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, h _ _ hp.2⟩
theorem card_lt_of_sub_image {α β : Type*} [DecidableEq α] [DecidableEq β] {s : Finset β}
    {t : Finset α} {a : α} (g : α → β) (ha : a ∈ t) (h : s ⊆ (t.erase a).image g) :
    s.card < t.card :=
  lt_of_le_of_lt ((card_le_card h).trans card_image_le) (card_erase_lt_of_mem ha)
theorem nl_rc {r : V → V → Prop} {x y : V} (hxy : x ≠ y) (hr : r x y) :
    nl (rc r x y) < nl r := by
  classical
  unfold nl
  apply card_lt_of_sub_image (Prod.map (fc x y) (fc x y)) (a := (x, y))
  · simp [hxy, hr]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨hne, p0, q0, h1, h2, h3⟩ := hp
    rw [mem_image]
    refine ⟨(p0, q0), ?_, ?_⟩
    · rw [mem_erase, mem_filter]
      refine ⟨?_, mem_univ _, ?_, h3⟩
      · intro h
        simp only [Prod.mk.injEq] at h
        apply hne
        rw [← h1, ← h2, h.1, h.2, fc_of_ne hxy, fc_y]
      · intro h
        apply hne
        rw [← h1, ← h2]
        exact congrArg (fc x y) h
    · simp [h1, h2]
theorem split_step {r : V → V → Prop} (hr : ∀ a b, r a b → r b a) {A B X : Finset V}
    (hX : IsSep r A B X) {x y : V} (hxy : x ≠ y) (hrxy : r x y) (hx : x ∈ X) (hy : y ∈ X)
    (ih : ∀ r' : V → V → Prop, (∀ a b, r' a b → r' b a) → nl r' < nl r →
      ∀ A B : Finset V, ∃ C, IsSep r' A B C ∧ ∃ F, IsPack r' A B F ∧ C.card ≤ F.card) :
    (∃ C, IsSep r A B C ∧ C.card < X.card) ∨ (∃ F, IsPack r A B F ∧ X.card ≤ F.card) := by
  let inA : V → Prop := fun p => p ∈ X ∨ ∃ a ∈ A, a ∉ X ∧ ReflTransGen (Av r X) a p
  let inB : V → Prop := fun p => p ∈ X ∨ ∃ b ∈ B, b ∉ X ∧ ReflTransGen (Av r X) b p
  let rA : V → V → Prop := fun p q => r p q ∧ inA p ∧ inA q ∧ ¬ (p ∈ X ∧ q ∈ X)
  let rB : V → V → Prop := fun p q => r p q ∧ inB p ∧ inB q ∧ ¬ (p ∈ X ∧ q ∈ X)
  have hrA : ∀ a b, rA a b → rA b a := fun a b h =>
    ⟨hr _ _ h.1, h.2.2.1, h.2.1, fun h' => h.2.2.2 ⟨h'.2, h'.1⟩⟩
  have hrB : ∀ a b, rB a b → rB b a := fun a b h =>
    ⟨hr _ _ h.1, h.2.2.1, h.2.1, fun h' => h.2.2.2 ⟨h'.2, h'.1⟩⟩
  have hnA : nl rA < nl r := nl_lt (fun p q h => h.1) hxy hrxy (fun h => h.2.2.2 ⟨hx, hy⟩)
  have hnB : nl rB < nl r := nl_lt (fun p q h => h.1) hxy hrxy (fun h => h.2.2.2 ⟨hx, hy⟩)
  obtain ⟨CA, hCA, FA, hFA, hCFA⟩ := ih rA hrA hnA A X
  obtain ⟨CB, hCB, FB, hFB, hCFB⟩ := ih rB hrB hnB X B
  have sub : ∀ (D : Finset V) (T : Finset V) (s z : V), s ∈ D → s ∈ T → z ∈ T → z ∈ X →
      Conn r T → ∃ T' ⊆ T, s ∈ T' ∧ (∃ z', T' ∩ X = {z'}) ∧
        Conn (fun p q => r p q ∧ (p ∈ X ∨ ∃ a ∈ D, a ∉ X ∧ ReflTransGen (Av r X) a p) ∧
          (q ∈ X ∨ ∃ a ∈ D, a ∉ X ∧ ReflTransGen (Av r X) a q) ∧ ¬ (p ∈ X ∧ q ∈ X)) T' := by
    intro D T s z hsD hsT hzT hzX hT
    obtain ⟨T', hT'T, hsT', ⟨z', hz'⟩, hcT', hreach⟩ := first_hit hr (hT s hsT z hzT) hsT hzX
    refine ⟨T', hT'T, hsT', ⟨z', hz'⟩, ?_⟩
    apply conn_of hcT'
    intro p hp q hq hpq hne
    refine ⟨hpq, ?_, ?_, ?_⟩
    · by_cases hpX : p ∈ X
      · exact Or.inl hpX
      · exact Or.inr ⟨s, hsD, av_src (hreach p hp hpX) hpX, hreach p hp hpX⟩
    · by_cases hqX : q ∈ X
      · exact Or.inl hqX
      · exact Or.inr ⟨s, hsD, av_src (hreach q hq hqX) hqX, hreach q hq hqX⟩
    · rintro ⟨hpX, hqX⟩
      have e1 : p ∈ T' ∩ X := mem_inter.2 ⟨hp, hpX⟩
      have e2 : q ∈ T' ∩ X := mem_inter.2 ⟨hq, hqX⟩
      rw [hz', mem_singleton] at e1 e2
      exact hne (e1.trans e2.symm)
  have sepA : IsSep r A B CA := by
    intro T hT
    obtain ⟨z, hz⟩ := hX T hT
    obtain ⟨⟨a, ha⟩, _, hcT⟩ := hT
    rw [mem_inter] at ha hz
    obtain ⟨T', hT'T, haT', ⟨z', hz'⟩, hc'⟩ := sub A T a z ha.2 ha.1 hz.1 hz.2 hcT
    obtain ⟨c, hc⟩ := hCA T' ⟨⟨a, mem_inter.2 ⟨haT', ha.2⟩⟩,
      ⟨z', by rw [hz']; exact mem_singleton_self _⟩, hc'⟩
    rw [mem_inter] at hc
    exact ⟨c, mem_inter.2 ⟨hT'T hc.1, hc.2⟩⟩
  have sepB : IsSep r A B CB := by
    intro T hT
    obtain ⟨z, hz⟩ := hX T hT
    obtain ⟨_, ⟨b, hb⟩, hcT⟩ := hT
    rw [mem_inter] at hb hz
    obtain ⟨T', hT'T, hbT', ⟨z', hz'⟩, hc'⟩ := sub B T b z hb.2 hb.1 hz.1 hz.2 hcT
    obtain ⟨c, hc⟩ := hCB T' ⟨⟨z', by rw [hz']; exact mem_singleton_self _⟩,
      ⟨b, mem_inter.2 ⟨hbT', hb.2⟩⟩, hc'⟩
    rw [mem_inter] at hc
    exact ⟨c, mem_inter.2 ⟨hT'T hc.1, hc.2⟩⟩
  by_cases hA' : CA.card < X.card
  · exact Or.inl ⟨CA, sepA, hA'⟩
  by_cases hB' : CB.card < X.card
  · exact Or.inl ⟨CB, sepB, hB'⟩
  push_neg at hA' hB'
  right
  refine comb hFA hFB (hA'.trans hCFA) (hB'.trans hCFB) (fun p q h => h.1) (fun p q h => h.1) ?_
  intro S hS T hT p hpS hpT
  by_contra hpX
  have hinA : inA p := by
    obtain ⟨_, ⟨z, hz⟩, hcS⟩ := hFA.1 S hS
    rw [mem_inter] at hz
    exact conn_in (P := inA) (fun p q h => h.2.2.1) hcS hz.1 (Or.inl hz.2) p hpS
  have hinB : inB p := by
    obtain ⟨⟨z, hz⟩, _, hcT⟩ := hFB.1 T hT
    rw [mem_inter] at hz
    exact conn_in (P := inB) (fun p q h => h.2.2.1) hcT hz.1 (Or.inl hz.2) p hpT
  rcases hinA with h | ⟨a, ha, haX, hap⟩
  · exact hpX h
  rcases hinB with h | ⟨b, hb, _, hbp⟩
  · exact hpX h
  exact comp_sep hr hX ha haX hb hap hbp
theorem menger_aux : ∀ (N : ℕ) (r : V → V → Prop), (∀ a b, r a b → r b a) → nl r = N →
    ∀ A B : Finset V, ∃ C, IsSep r A B C ∧ ∃ F, IsPack r A B F ∧ C.card ≤ F.card := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro r hr hN A B
  have ih' : ∀ r' : V → V → Prop, (∀ a b, r' a b → r' b a) → nl r' < nl r →
      ∀ A B : Finset V, ∃ C, IsSep r' A B C ∧ ∃ F, IsPack r' A B F ∧ C.card ≤ F.card :=
    fun r' hr' hlt => ih (nl r') (by rw [← hN]; exact hlt) r' hr' rfl
  by_cases h0 : ∀ a b, r a b → a = b
  · exact menger_base r h0 A B
  push_neg at h0
  obtain ⟨x, y, hrxy, hxy⟩ := h0
  have hrc : ∀ a b, rc r x y a b → rc r x y b a := fun a b ⟨p0, q0, h1, h2, h3⟩ =>
    ⟨q0, p0, h2, h1, hr _ _ h3⟩
  obtain ⟨C1, hC1, F1, hF1, hCF⟩ := ih' (rc r x y) hrc (nl_rc hxy hrxy) (A.image (fc x y))
    (B.image (fc x y))
  obtain ⟨X, F, hX, hF, hXF, hor⟩ := contr_step hr hxy hrxy hC1 hF1 hCF
  rcases hor with h | ⟨hx, hy⟩
  · exact ⟨X, hX, F, hF, h⟩
  rcases split_step hr hX hxy hrxy hx hy ih' with ⟨C, hC, hCX⟩ | ⟨F', hF', hXF'⟩
  · exact ⟨C, hC, F, hF, by omega⟩
  · exact ⟨X, hX, F', hF', hXF'⟩
theorem menger (r : V → V → Prop) (hr : ∀ a b, r a b → r b a) (A B : Finset V) :
    ∃ C, IsSep r A B C ∧ ∃ F, IsPack r A B F ∧ C.card ≤ F.card :=
  menger_aux _ r hr rfl A B
end G
theorem pack_card_le {V : Type*} [DecidableEq V] {r : V → V → Prop} {A B : Finset V}
    {F : Finset (Finset V)} (hF : IsPack r A B F) : F.card ≤ A.card := by
  have h1 : (F.biUnion (fun S => S ∩ A)).card = ∑ S ∈ F, (S ∩ A).card :=
    card_biUnion (fun S hS T hT h =>
      Disjoint.mono inter_subset_left inter_subset_left (hF.2 S hS T hT h))
  have h2 : F.biUnion (fun S => S ∩ A) ⊆ A := biUnion_subset.2 (fun S _ => inter_subset_right)
  have h3 : ∑ S ∈ F, 1 ≤ ∑ S ∈ F, (S ∩ A).card :=
    sum_le_sum (fun S hS => Nat.succ_le_of_lt (card_pos.2 (hF.1 S hS).1))
  simp only [sum_const, smul_eq_mul, mul_one] at h3
  have := card_le_card h2
  omega
def adjR {n m : ℕ} (u v : Fin m → Fin n) (a b : Fin n) : Prop :=
  ∃ e, (u e = a ∧ v e = b) ∨ (u e = b ∧ v e = a)
def matR {n m : ℕ} (u v : Fin m → Fin n) (A B : Finset (Fin n)) (w : Fin m → ℚ) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) ℚ :=
  fun P Q => ∑ x : Fin n → Bool,
    if (∀ i ∈ A ∩ P, x i = false) ∧ (∀ i ∈ B ∩ Q, x i = false) then
      ∏ e, (if x (u e) = x (v e) then 1 else w e) else 0
theorem factor_sum {n : ℕ} (C L : Finset (Fin n)) (hLC : ∀ i ∈ L, i ∉ C)
    (f g : (Fin n → Bool) → ℚ)
    (hf : ∀ x x', (∀ i, i ∈ C ∨ i ∈ L → x i = x' i) → f x = f x')
    (hg : ∀ x x', (∀ i, i ∉ L → x i = x' i) → g x = g x') :
    ∑ c : C → Bool, (∑ x : Fin n → Bool, if (∀ i : C, x i = c i) ∧
        (∀ i, i ∉ C → i ∉ L → x i = false) then f x else 0) *
      (∑ x : Fin n → Bool, if (∀ i : C, x i = c i) ∧ (∀ i ∈ L, x i = false) then g x else 0) =
    ∑ y, f y * g y := by
  have step1 : ∀ x x' : Fin n → Bool, ∑ c : C → Bool,
      (if (∀ i : C, x i = c i) ∧ (∀ i, i ∉ C → i ∉ L → x i = false) then f x else 0) *
      (if (∀ i : C, x' i = c i) ∧ (∀ i ∈ L, x' i = false) then g x' else 0) =
      if ((∀ i, i ∉ C → i ∉ L → x i = false) ∧ (∀ i ∈ L, x' i = false)) ∧
        (∀ i : C, x' i = x i) then f x * g x' else 0 := by
    intro x x'
    rw [Finset.sum_eq_single (fun i : C => x i)]
    · show (if (∀ i : C, x i = x i) ∧ (∀ i, i ∉ C → i ∉ L → x i = false) then f x else 0) *
          (if (∀ i : C, x' i = x i) ∧ (∀ i ∈ L, x' i = false) then g x' else 0) = _
      by_cases h1 : ∀ i, i ∉ C → i ∉ L → x i = false
      · rw [if_pos ⟨fun i => rfl, h1⟩]
        by_cases h2 : ∀ i ∈ L, x' i = false
        · by_cases h3 : ∀ i : C, x' i = x i
          · rw [if_pos ⟨h3, h2⟩, if_pos ⟨⟨h1, h2⟩, h3⟩]
          · rw [if_neg (fun h => h3 h.1), if_neg (fun h => h3 h.2), mul_zero]
        · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.1.2), mul_zero]
      · rw [if_neg (fun h => h1 h.2), zero_mul, eq_comm]
        exact if_neg (fun h => h1 h.1.1)
    · intro c _ hc
      rw [if_neg, zero_mul]
      rintro ⟨h1, _⟩
      exact hc (funext fun i => (h1 i).symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  calc _ = ∑ c : C → Bool, ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool,
        (if (∀ i : C, x i = c i) ∧ (∀ i, i ∉ C → i ∉ L → x i = false) then f x else 0) *
        (if (∀ i : C, x' i = c i) ∧ (∀ i ∈ L, x' i = false) then g x' else 0) := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.sum_mul_sum]
    _ = ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool, ∑ c : C → Bool,
        (if (∀ i : C, x i = c i) ∧ (∀ i, i ∉ C → i ∉ L → x i = false) then f x else 0) *
        (if (∀ i : C, x' i = c i) ∧ (∀ i ∈ L, x' i = false) then g x' else 0) :=
          (Finset.sum_comm).trans (Finset.sum_congr rfl (fun x _ => Finset.sum_comm))
    _ = ∑ x : Fin n → Bool, ∑ x' : Fin n → Bool,
        if ((∀ i, i ∉ C → i ∉ L → x i = false) ∧ (∀ i ∈ L, x' i = false)) ∧
          (∀ i : C, x' i = x i) then f x * g x' else 0 :=
          Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => step1 x x'))
    _ = ∑ p ∈ (univ ×ˢ univ : Finset ((Fin n → Bool) × (Fin n → Bool))).filter
          (fun p => ((∀ i, i ∉ C → i ∉ L → p.1 i = false) ∧ (∀ i ∈ L, p.2 i = false)) ∧
            (∀ i : C, p.2 i = p.1 i)), f p.1 * g p.2 := by
          rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ y, f y * g y := by
          symm
          apply Finset.sum_nbij' (fun y => ((fun i => if i ∈ C ∨ i ∈ L then y i else false),
            (fun i => if i ∈ L then false else y i)))
            (fun p => fun i => if i ∈ L then p.1 i else p.2 i)
          · intro y _
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
            refine ⟨⟨fun i hiC hiL => ?_, fun i hiL => ?_⟩, fun i => ?_⟩
            · simp [hiC, hiL]
            · simp [hiL]
            · have h1 : (i : Fin n) ∉ L := fun h => hLC _ h i.2
              simp [h1, i.2]
          · intro p _; exact Finset.mem_univ _
          · intro y _
            funext i
            by_cases hiL : i ∈ L <;> simp [hiL]
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
            obtain ⟨⟨h1, h2⟩, h3⟩ := hp
            refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
            · by_cases hiL : i ∈ L
              · simp [hiL]
              · by_cases hiC : i ∈ C
                · have := h3 ⟨i, hiC⟩
                  simp only at this
                  simp [hiL, hiC, this]
                · simp [hiL, hiC, h1 i hiC hiL]
            · by_cases hiL : i ∈ L
              · simp [hiL, h2 i hiL]
              · simp [hiL]
          · intro y _
            congr 1
            · apply hf; intro i hi; simp [hi]
            · apply hg; intro i hi; simp [hi]
theorem rank_le_sep {n m : ℕ} (u v : Fin m → Fin n) (A B C : Finset (Fin n))
    (hC : IsSep (adjR u v) A B C) (w : Fin m → ℚ) : (matR u v A B w).rank ≤ 2 ^ C.card := by
  have hsym : ∀ a b, adjR u v a b → adjR u v b a := fun a b h => by
    obtain ⟨e, he⟩ := h; exact ⟨e, he.symm⟩
  let L : Finset (Fin n) := @Finset.filter _
    (fun i => ∃ a ∈ A, a ∉ C ∧ ReflTransGen (Av (adjR u v) C) a i) (Classical.decPred _) univ
  have hL : ∀ i, i ∈ L ↔ ∃ a ∈ A, a ∉ C ∧ ReflTransGen (Av (adjR u v) C) a i := fun i => by
    simp [L]
  have hLC : ∀ i ∈ L, i ∉ C := by
    intro i hi
    obtain ⟨a, _, haC, hai⟩ := (hL i).1 hi
    exact rtg_avoid hai haC
  have hLB : ∀ i ∈ L, i ∉ B := by
    intro i hi hiB
    obtain ⟨a, haA, haC, hai⟩ := (hL i).1 hi
    exact comp_sep hsym hC haA haC hiB hai ReflTransGen.refl
  have hAL : ∀ i ∈ A, i ∉ C → i ∈ L := fun i hi hiC => (hL i).2 ⟨i, hi, hiC, ReflTransGen.refl⟩
  have hLe : ∀ i j, i ∈ L → adjR u v i j → j ∉ C → j ∈ L := by
    intro i j hi hij hjC
    obtain ⟨a, haA, haC, hai⟩ := (hL i).1 hi
    exact (hL j).2 ⟨a, haA, haC, hai.tail ⟨hLC i hi, hjC, hij⟩⟩
  let EL : Finset (Fin m) := univ.filter (fun e => u e ∈ L ∨ v e ∈ L)
  have hEL1 : ∀ e ∈ EL, (u e ∈ C ∨ u e ∈ L) ∧ (v e ∈ C ∨ v e ∈ L) := by
    intro e he
    simp only [EL, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with h | h
    · refine ⟨Or.inr h, ?_⟩
      by_cases hv : v e ∈ C
      · exact Or.inl hv
      · exact Or.inr (hLe _ _ h ⟨e, Or.inl ⟨rfl, rfl⟩⟩ hv)
    · refine ⟨?_, Or.inr h⟩
      by_cases hu : u e ∈ C
      · exact Or.inl hu
      · exact Or.inr (hLe _ _ h ⟨e, Or.inr ⟨rfl, rfl⟩⟩ hu)
  have hEL2 : ∀ e ∉ EL, u e ∉ L ∧ v e ∉ L := by
    intro e he
    simp only [EL, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at he
    exact he
  let f : Finset (Fin n) → (Fin n → Bool) → ℚ := fun P x =>
    (if ∀ i ∈ A ∩ P, x i = false then 1 else 0) *
      ∏ e ∈ EL, (if x (u e) = x (v e) then 1 else w e)
  let g : Finset (Fin n) → (Fin n → Bool) → ℚ := fun Q x =>
    (if ∀ i ∈ B ∩ Q, x i = false then 1 else 0) *
      ∏ e ∈ ELᶜ, (if x (u e) = x (v e) then 1 else w e)
  have hmat : ∀ P Q, matR u v A B w P Q = ∑ x, f P x * g Q x := by
    intro P Q
    unfold matR
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.prod_mul_prod_compl EL]
    simp only [f, g]
    by_cases h1 : ∀ i ∈ A ∩ P, x i = false
    · by_cases h2 : ∀ i ∈ B ∩ Q, x i = false
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]; ring
      · rw [if_neg (fun h => h2 h.2), if_neg h2]; ring
    · rw [if_neg (fun h => h1 h.1), if_neg h1]; ring
  have hf : ∀ P x x', (∀ i, i ∈ C ∨ i ∈ L → x i = x' i) → f P x = f P x' := by
    intro P x x' hxx
    have hc : (∀ i ∈ A ∩ P, x i = false) ↔ (∀ i ∈ A ∩ P, x' i = false) := by
      have hA : ∀ i ∈ A ∩ P, i ∈ C ∨ i ∈ L := by
        intro i hi
        by_cases hiC : i ∈ C
        · exact Or.inl hiC
        · exact Or.inr (hAL i (Finset.mem_inter.1 hi).1 hiC)
      constructor
      · intro h i hi; rw [← hxx i (hA i hi)]; exact h i hi
      · intro h i hi; rw [hxx i (hA i hi)]; exact h i hi
    have hp : ∏ e ∈ EL, (if x (u e) = x (v e) then (1:ℚ) else w e) =
        ∏ e ∈ EL, (if x' (u e) = x' (v e) then 1 else w e) := by
      refine Finset.prod_congr rfl (fun e he => ?_)
      rw [hxx _ (hEL1 e he).1, hxx _ (hEL1 e he).2]
    simp only [f, hp]
    by_cases h1 : ∀ i ∈ A ∩ P, x i = false
    · rw [if_pos h1, if_pos (hc.1 h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (hc.2 h))]
  have hg : ∀ Q x x', (∀ i, i ∉ L → x i = x' i) → g Q x = g Q x' := by
    intro Q x x' hxx
    have hc : (∀ i ∈ B ∩ Q, x i = false) ↔ (∀ i ∈ B ∩ Q, x' i = false) := by
      have hB : ∀ i ∈ B ∩ Q, i ∉ L := fun i hi hiL => hLB i hiL (Finset.mem_inter.1 hi).1
      constructor
      · intro h i hi; rw [← hxx i (hB i hi)]; exact h i hi
      · intro h i hi; rw [hxx i (hB i hi)]; exact h i hi
    have hp : ∏ e ∈ ELᶜ, (if x (u e) = x (v e) then (1:ℚ) else w e) =
        ∏ e ∈ ELᶜ, (if x' (u e) = x' (v e) then 1 else w e) := by
      refine Finset.prod_congr rfl (fun e he => ?_)
      have he' := hEL2 e (Finset.mem_compl.1 he)
      rw [hxx _ he'.1, hxx _ he'.2]
    simp only [g, hp]
    by_cases h1 : ∀ i ∈ B ∩ Q, x i = false
    · rw [if_pos h1, if_pos (hc.1 h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (hc.2 h))]
  let Fm : Matrix (Finset (Fin n)) (C → Bool) ℚ := fun P c => ∑ x : Fin n → Bool,
    if (∀ i : C, x i = c i) ∧ (∀ i, i ∉ C → i ∉ L → x i = false) then f P x else 0
  let Gm : Matrix (C → Bool) (Finset (Fin n)) ℚ := fun c Q => ∑ x : Fin n → Bool,
    if (∀ i : C, x i = c i) ∧ (∀ i ∈ L, x i = false) then g Q x else 0
  have hFG : matR u v A B w = Fm * Gm := by
    ext P Q
    rw [hmat, Matrix.mul_apply]
    exact (factor_sum C L hLC (f P) (g Q) (hf P) (hg Q)).symm
  rw [hFG]
  calc (Fm * Gm).rank ≤ Fm.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (C → Bool) := Matrix.rank_le_card_width _
    _ = 2 ^ C.card := by simp
theorem psd_kernel {ι κ : Type*} [Fintype ι] [Fintype κ] (ω : κ → ℚ) (hω : ∀ x, 0 ≤ ω x)
    (t : κ → ι → ℚ) (v : ι → ℚ)
    (h : ∀ α, ∑ β, (∑ x, ω x * t x α * t x β) * v β = 0) :
    ∀ x, ω x ≠ 0 → ∑ α, t x α * v α = 0 := by
  have hq : ∑ x, ω x * ((∑ α, t x α * v α) * (∑ α, t x α * v α)) = 0 := by
    have h0 : ∑ α, v α * ∑ β, (∑ x, ω x * t x α * t x β) * v β = 0 := by simp [h]
    rw [← h0]
    calc ∑ x, ω x * ((∑ α, t x α * v α) * (∑ α, t x α * v α))
        = ∑ x, ∑ α, ∑ β, v α * (ω x * t x α * t x β * v β) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun β _ => ?_)
          ring
      _ = ∑ α, ∑ x, ∑ β, v α * (ω x * t x α * t x β * v β) := Finset.sum_comm
      _ = ∑ α, ∑ β, ∑ x, v α * (ω x * t x α * t x β * v β) :=
          Finset.sum_congr rfl (fun α _ => Finset.sum_comm)
      _ = ∑ α, v α * ∑ β, (∑ x, ω x * t x α * t x β) * v β := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun β _ => ?_)
          rw [Finset.sum_mul, Finset.mul_sum]
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => mul_nonneg (hω x) (mul_self_nonneg _))).1 hq
  intro x hx
  rcases mul_eq_zero.1 (h2 x (Finset.mem_univ _)) with h3 | h3
  · exact absurd h3 hx
  · exact mul_self_eq_zero.1 h3
theorem zeta_inj {T : Type*} [DecidableEq T] (F : Finset T) (v : ↥F.powerset → ℚ)
    (h : ∀ γ ∈ F.powerset, ∑ α : ↥F.powerset, (if α.1 ⊆ γ then v α else 0) = 0) : v = 0 := by
  have key : ∀ γ : Finset T, ∀ hγ : γ ∈ F.powerset, v ⟨γ, hγ⟩ = 0 := by
    intro γ
    induction γ using Finset.strongInduction with
    | H γ ih =>
      intro hγ
      have h1 := h γ hγ
      rw [Finset.sum_eq_single ⟨γ, hγ⟩] at h1
      · simpa using h1
      · intro α _ hne
        split_ifs with hsub
        · exact ih α.1 (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => hne (Subtype.ext h)⟩) α.2
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
  funext α
  exact key α.1 α.2
theorem lower {n m : ℕ} (u v : Fin m → Fin n) (A B : Finset (Fin n))
    (F : Finset (Finset (Fin n))) (hF : IsPack (adjR u v) A B F) :
    ∃ p : MvPolynomial (Fin m) ℚ, p ≠ 0 ∧ (∀ e, p.degreeOf e ≤ 2 ^ F.card) ∧
      ∀ w, MvPolynomial.eval w p ≠ 0 → 2 ^ F.card ≤ (matR u v A B w).rank := by
  let rsel : ↥F.powerset → Finset (Fin n) := fun α => α.1.biUnion id
  let MP : Matrix (Finset (Fin n)) (Finset (Fin n)) (MvPolynomial (Fin m) ℚ) := fun P Q =>
    ∑ x : Fin n → Bool, if (∀ i ∈ A ∩ P, x i = false) ∧ (∀ i ∈ B ∩ Q, x i = false) then
      ∏ e, (if x (u e) = x (v e) then 1 else MvPolynomial.X e) else 0
  have hMP : ∀ w : Fin m → ℚ, MP.map (MvPolynomial.eval w) = matR u v A B w := by
    intro w
    ext P Q
    rw [Matrix.map_apply]
    simp only [MP, matR]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs
    · rw [map_prod]
      refine Finset.prod_congr rfl (fun e _ => ?_)
      split_ifs <;> simp
    · simp
  have hev : ∀ w : Fin m → ℚ, MvPolynomial.eval w (MP.submatrix rsel rsel).det =
      ((matR u v A B w).submatrix rsel rsel).det := by
    intro w
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hMP w]
    rfl
  let wstar : Fin m → ℚ := fun e => if ∃ S ∈ F, u e ∈ S ∧ v e ∈ S then 0 else 1
  have hmem : ∀ γ : Finset (Finset (Fin n)), ∀ S ∈ F, ∀ i ∈ S,
      (∃ S' ∈ F, S' ∉ γ ∧ i ∈ S') ↔ S ∉ γ := by
    intro γ S hS i hi
    constructor
    · rintro ⟨S', hS', hS'γ, hiS'⟩
      by_cases hSS' : S = S'
      · rw [hSS']; exact hS'γ
      · exact absurd hiS' (Finset.disjoint_left.1 (hF.2 S hS S' hS' hSS') hi)
    · intro h; exact ⟨S, hS, h, hi⟩
  have hN : ((matR u v A B wstar).submatrix rsel rsel).det ≠ 0 := by
    intro h0
    obtain ⟨vv, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    let ω : (Fin n → Bool) → ℚ := fun x => ∏ e, (if x (u e) = x (v e) then 1 else wstar e)
    let t : (Fin n → Bool) → ↥F.powerset → ℚ := fun x α =>
      if ∀ i ∈ rsel α, x i = false then 1 else 0
    have hω0 : ∀ x, 0 ≤ ω x := fun x => Finset.prod_nonneg (fun e _ => by
      simp only [wstar]; split_ifs <;> norm_num)
    have hconst : ∀ x, ω x ≠ 0 → ∀ S ∈ F, ∀ i ∈ S, ∀ j ∈ S, x i = x j := by
      intro x hx S hS i hi j hj
      have hfac : ∀ e, (if x (u e) = x (v e) then (1:ℚ) else wstar e) ≠ 0 :=
        fun e => Finset.prod_ne_zero_iff.1 hx e (Finset.mem_univ _)
      have hedge : ∀ e, u e ∈ S → v e ∈ S → x (u e) = x (v e) := by
        intro e hu hv'
        by_contra hne
        apply hfac e
        rw [if_neg hne]
        simp only [wstar]
        rw [if_pos ⟨S, hS, hu, hv'⟩]
      have hc := (hF.1 S hS).2.2 i hi j hj
      induction hc with
      | refl => rfl
      | tail _ hbc ih =>
        obtain ⟨hb, hc', e, he⟩ := hbc
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [ih hb, ← h1, ← h2]
          exact hedge e (by rw [h1]; exact hb) (by rw [h2]; exact hc')
        · rw [ih hb, ← h1, ← h2]
          exact (hedge e (by rw [h1]; exact hc') (by rw [h2]; exact hb)).symm
    have hiff : ∀ x, ω x ≠ 0 → ∀ α : ↥F.powerset,
        ((∀ i ∈ A ∩ rsel α, x i = false) ↔ (∀ i ∈ rsel α, x i = false)) ∧
        ((∀ i ∈ B ∩ rsel α, x i = false) ↔ (∀ i ∈ rsel α, x i = false)) := by
      intro x hx α
      have hαF : α.1 ⊆ F := Finset.mem_powerset.1 α.2
      constructor
      · constructor
        · intro h i hi
          obtain ⟨S, hSα, hiS⟩ := Finset.mem_biUnion.1 hi
          obtain ⟨a, ha⟩ := (hF.1 S (hαF hSα)).1
          rw [Finset.mem_inter] at ha
          rw [hconst x hx S (hαF hSα) i hiS a ha.1]
          exact h a (Finset.mem_inter.2 ⟨ha.2, Finset.mem_biUnion.2 ⟨S, hSα, ha.1⟩⟩)
        · intro h i hi; exact h i (Finset.mem_inter.1 hi).2
      · constructor
        · intro h i hi
          obtain ⟨S, hSα, hiS⟩ := Finset.mem_biUnion.1 hi
          obtain ⟨a, ha⟩ := (hF.1 S (hαF hSα)).2.1
          rw [Finset.mem_inter] at ha
          rw [hconst x hx S (hαF hSα) i hiS a ha.1]
          exact h a (Finset.mem_inter.2 ⟨ha.2, Finset.mem_biUnion.2 ⟨S, hSα, ha.1⟩⟩)
        · intro h i hi; exact h i (Finset.mem_inter.1 hi).2
    have hkey : ∀ x (α β : ↥F.powerset), (if (∀ i ∈ A ∩ rsel α, x i = false) ∧
        (∀ i ∈ B ∩ rsel β, x i = false) then ω x else 0) = ω x * t x α * t x β := by
      intro x α β
      by_cases hx : ω x = 0
      · rw [hx]; simp
      · have e1 : (∀ i ∈ A ∩ rsel α, x i = false) ∧ (∀ i ∈ B ∩ rsel β, x i = false) ↔
            (∀ i ∈ rsel α, x i = false) ∧ (∀ i ∈ rsel β, x i = false) :=
          and_congr (hiff x hx α).1 (hiff x hx β).2
        simp only [t]
        by_cases h1 : ∀ i ∈ rsel α, x i = false <;> by_cases h2 : ∀ i ∈ rsel β, x i = false
        · rw [if_pos (e1.2 ⟨h1, h2⟩), if_pos h1, if_pos h2]; ring
        · rw [if_neg (fun h => h2 (e1.1 h).2), if_pos h1, if_neg h2]; ring
        · rw [if_neg (fun h => h1 (e1.1 h).1), if_neg h1, if_pos h2]; ring
        · rw [if_neg (fun h => h1 (e1.1 h).1), if_neg h1, if_neg h2]; ring
    have hrow : ∀ α, ∑ β, (∑ x, ω x * t x α * t x β) * vv β = 0 := by
      intro α
      have h1 := congrFun hv α
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, matR, Pi.zero_apply] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      congr 1
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact (hkey x α β).symm
    have hker := psd_kernel ω hω0 t vv hrow
    refine zeta_inj F vv (fun γ _ => ?_)
    let xγ : Fin n → Bool := fun i => decide (∃ S ∈ F, S ∉ γ ∧ i ∈ S)
    have hωγ : ω xγ = 1 := by
      apply Finset.prod_eq_one
      intro e _
      by_cases hagree : xγ (u e) = xγ (v e)
      · rw [if_pos hagree]
      · rw [if_neg hagree]
        simp only [wstar]
        rw [if_neg]
        rintro ⟨S, hS, hu, hv'⟩
        apply hagree
        simp only [xγ]
        rw [decide_eq_decide, hmem γ S hS _ hu, hmem γ S hS _ hv']
    have htγ : ∀ α : ↥F.powerset, t xγ α = if α.1 ⊆ γ then 1 else 0 := by
      intro α
      have hαF : α.1 ⊆ F := Finset.mem_powerset.1 α.2
      simp only [t]
      have e1 : (∀ i ∈ rsel α, xγ i = false) ↔ α.1 ⊆ γ := by
        constructor
        · intro h S hSα
          by_contra hSγ
          obtain ⟨a, ha⟩ := (hF.1 S (hαF hSα)).1
          have haS := (Finset.mem_inter.1 ha).1
          have h3 := h a (Finset.mem_biUnion.2 ⟨S, hSα, haS⟩)
          simp only [xγ, decide_eq_false_iff_not] at h3
          exact h3 ((hmem γ S (hαF hSα) a haS).2 hSγ)
        · intro h i hi
          obtain ⟨S, hSα, hiS⟩ := Finset.mem_biUnion.1 hi
          simp only [xγ, decide_eq_false_iff_not]
          rw [hmem γ S (hαF hSα) i hiS]
          exact not_not.2 (h hSα)
      by_cases h1 : α.1 ⊆ γ
      · rw [if_pos (e1.2 h1), if_pos h1]
      · rw [if_neg (fun h => h1 (e1.1 h)), if_neg h1]
    have h4 := hker xγ (by rw [hωγ]; norm_num)
    refine Eq.trans ?_ h4
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [htγ α]
    split_ifs <;> ring
  refine ⟨(MP.submatrix rsel rsel).det, ?_, ?_, ?_⟩
  · intro h0
    have h1 := hev wstar
    rw [h0, map_zero] at h1
    exact hN h1.symm
  · intro e
    have hentry : ∀ P Q, (MP P Q).degreeOf e ≤ 1 := by
      intro P Q
      refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le (fun x _ => ?_))
      split_ifs
      · refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
        calc ∑ e' : Fin m, (if x (u e') = x (v e') then (1 : MvPolynomial (Fin m) ℚ)
              else MvPolynomial.X e').degreeOf e
            ≤ ∑ e' : Fin m, if e = e' then 1 else 0 := by
              refine Finset.sum_le_sum (fun e' _ => ?_)
              split_ifs <;> simp_all [MvPolynomial.degreeOf_X]
          _ = 1 := by simp
      · simp
    rw [Matrix.det_apply]
    refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le (fun σ _ => ?_))
    have hprod : (∏ i, (MP.submatrix rsel rsel) (σ i) i).degreeOf e ≤ 2 ^ F.card := by
      refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
      calc ∑ i, ((MP.submatrix rsel rsel) (σ i) i).degreeOf e ≤ ∑ i : ↥F.powerset, 1 :=
            Finset.sum_le_sum (fun i _ => hentry _ _)
        _ = 2 ^ F.card := by simp [Finset.card_powerset]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]; exact hprod
    · rw [h, Units.neg_smul, one_smul, MvPolynomial.degreeOf_neg]; exact hprod
  · intro w hw
    rw [hev] at hw
    have h1 := Matrix.rank_submatrix_le (matR u v A B w) rsel rsel
    have h2 : ((matR u v A B w).submatrix rsel rsel).rank = Fintype.card ↥F.powerset :=
      Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hw))
    rw [Fintype.card_coe, Finset.card_powerset] at h2
    omega
end PEqualNP.Outside.L_lib_998
theorem PEqualNP.Outside.L_lib_998 : ∀ (n m : ℕ) (u v : Fin m → Fin n),
  let I := Fin n
  let X := I → Bool
  let adj := fun a b : I => ∃ e, (u e = a ∧ v e = b) ∨ (u e = b ∧ v e = a)
  let pack := fun (A B : Finset I) (F : Finset (Finset I)) =>
    (∀ S ∈ F, (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty ∧
      ∀ i ∈ S, ∀ j ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ adj x y) i j) ∧
    ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T
  let k := fun A B => ((Finset.univ : Finset (Finset (Finset I))).filter
    (fun F => @decide (pack A B F) (Classical.propDecidable _))).sup Finset.card
  let mat := fun (A B : Finset I) (w : Fin m → ℚ) =>
    (fun (P Q : Finset I) => ∑ x : X,
      if (∀ i ∈ A ∩ P, x i = false) ∧ (∀ i ∈ B ∩ Q, x i = false) then
        ∏ e, (if x (u e) = x (v e) then 1 else w e) else 0 :
      Matrix (Finset I) (Finset I) ℚ)
  (∀ (A B : Finset I), Disjoint A B → ∀ w, Matrix.rank (mat A B w) ≤ 2^(k A B)) ∧
    ∀ U : Finset I, ∃ z : Fin m → ℕ, (∀ e, 2 ≤ z e ∧ z e ≤ (m+1)*8^(U.card+1)) ∧
      ∀ (A B : Finset I), A ⊆ U → B ⊆ U → Disjoint A B →
        Matrix.rank (mat A B (fun e => (z e : ℚ))) = 2^(k A B) := by
  intro n m u v I X adj pack k mat
  have hk_le : ∀ A B F, PEqualNP.Outside.L_lib_998.IsPack (PEqualNP.Outside.L_lib_998.adjR u v) A B F → F.card ≤ k A B := by
    intro A B F hF
    exact Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, @decide_eq_true _ (Classical.propDecidable _) hF⟩)
  have hk_att : ∀ A B, ∃ F, PEqualNP.Outside.L_lib_998.IsPack (PEqualNP.Outside.L_lib_998.adjR u v) A B F ∧ F.card = k A B := by
    intro A B
    have hne : (Finset.univ.filter
        (fun F => @decide (pack A B F) (Classical.propDecidable _))).Nonempty :=
      ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, @decide_eq_true _ (Classical.propDecidable _)
        ⟨fun S hS => by simp at hS, fun S hS => by simp at hS⟩⟩⟩
    obtain ⟨F, hF, hFk⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
    exact ⟨F, @of_decide_eq_true _ (Classical.propDecidable _) (Finset.mem_filter.1 hF).2,
      hFk.symm⟩
  have hkA : ∀ A B, k A B ≤ A.card := by
    intro A B
    obtain ⟨F, hF, hFk⟩ := hk_att A B
    rw [← hFk]
    exact PEqualNP.Outside.L_lib_998.pack_card_le hF
  have part1 : ∀ (A B : Finset (Fin n)), Disjoint A B → ∀ w,
      Matrix.rank (mat A B w) ≤ 2 ^ (k A B) := by
    intro A B _ w
    obtain ⟨C, hC, F, hF, hCF⟩ := PEqualNP.Outside.L_lib_998.menger (PEqualNP.Outside.L_lib_998.adjR u v)
      (fun a b h => by obtain ⟨e, he⟩ := h; exact ⟨e, he.symm⟩) A B
    exact (PEqualNP.Outside.L_lib_998.rank_le_sep u v A B C hC w).trans
      (Nat.pow_le_pow_right (by norm_num) (hCF.trans (hk_le A B F hF)))
  refine ⟨part1, fun U => ?_⟩
  have hpoly : ∀ A B : Finset (Fin n), ∃ p : MvPolynomial (Fin m) ℚ, p ≠ 0 ∧
      (∀ e, p.degreeOf e ≤ 2 ^ (k A B)) ∧
      ∀ w, MvPolynomial.eval w p ≠ 0 → 2 ^ (k A B) ≤ Matrix.rank (mat A B w) := by
    intro A B
    obtain ⟨F, hF, hFk⟩ := hk_att A B
    rw [← hFk]
    exact PEqualNP.Outside.L_lib_998.lower u v A B F hF
  choose p hp0 hpd hpe using hpoly
  have hQ0 : (∏ ab ∈ U.powerset ×ˢ U.powerset, p ab.1 ab.2) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun ab _ => hp0 ab.1 ab.2)
  have hQd : ∀ e, (∏ ab ∈ U.powerset ×ˢ U.powerset, p ab.1 ab.2).degreeOf e ≤ 8 ^ U.card := by
    intro e
    calc (∏ ab ∈ U.powerset ×ˢ U.powerset, p ab.1 ab.2).degreeOf e
        ≤ ∑ ab ∈ U.powerset ×ˢ U.powerset, (p ab.1 ab.2).degreeOf e :=
          MvPolynomial.degreeOf_prod_le _ _ _
      _ ≤ ∑ ab ∈ U.powerset ×ˢ U.powerset, 2 ^ U.card := by
          apply Finset.sum_le_sum
          intro ab hab
          rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hab
          exact (hpd ab.1 ab.2 e).trans (Nat.pow_le_pow_right (by norm_num)
            ((hkA ab.1 ab.2).trans (Finset.card_le_card hab.1)))
      _ = 8 ^ U.card := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_powerset, smul_eq_mul,
            ← mul_pow, ← mul_pow]
          norm_num
  have hcardS : ∀ e : Fin m, ((Finset.Icc 2 ((m + 1) * 8 ^ (U.card + 1))).image
      (fun t : ℕ => (t : ℚ))).card = (m + 1) * 8 ^ (U.card + 1) + 1 - 2 := by
    intro e
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]
  have hdeg : ∀ e, (∏ ab ∈ U.powerset ×ˢ U.powerset, p ab.1 ab.2).degreeOf e <
      ((Finset.Icc 2 ((m + 1) * 8 ^ (U.card + 1))).image (fun t : ℕ => (t : ℚ))).card := by
    intro e
    rw [hcardS e]
    have h1 : 1 ≤ 8 ^ U.card := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 8 * 8 ^ U.card ≤ (m + 1) * 8 ^ (U.card + 1) := by
      rw [pow_succ]; nlinarith
    have := hQd e
    omega
  obtain ⟨x, hxS, hx⟩ : ∃ x : Fin m → ℚ, (∀ e, x e ∈
      (Finset.Icc 2 ((m + 1) * 8 ^ (U.card + 1))).image (fun t : ℕ => (t : ℚ))) ∧
      MvPolynomial.eval x (∏ ab ∈ U.powerset ×ˢ U.powerset, p ab.1 ab.2) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ0 (MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ _ hdeg hcon)
  have hz : ∀ e, ∃ t : ℕ, t ∈ Finset.Icc 2 ((m + 1) * 8 ^ (U.card + 1)) ∧ (t : ℚ) = x e :=
    fun e => Finset.mem_image.1 (hxS e)
  choose z hzI hzx using hz
  refine ⟨z, fun e => Finset.mem_Icc.1 (hzI e), fun A B hA hB hAB => ?_⟩
  have hw : (fun e => (z e : ℚ)) = x := funext hzx
  apply le_antisymm (part1 A B hAB _)
  rw [hw]
  apply hpe A B x
  intro h0
  apply hx
  rw [map_prod]
  exact Finset.prod_eq_zero (i := (A, B)) (Finset.mem_product.2 ⟨Finset.mem_powerset.2 hA,
    Finset.mem_powerset.2 hB⟩) h0
