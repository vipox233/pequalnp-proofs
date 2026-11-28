import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

namespace PEqualNP.Outside.L_lib_1205_aux

def tip (z y b : Bool) : Bool :=
  if z then if b then !y else y else true

def adj {V : Type} (R : V → V → Prop) (p q : V × Bool) : Prop :=
  p.2 ≠ q.2 ∧ (p.1 = q.1 ∨ if p.2 then R p.1 q.1 else R q.1 p.1)

lemma adj_comm {V : Type} (R : V → V → Prop) (p q : V × Bool) :
    adj R p q ↔ adj R q p := by
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  cases a <;> cases b <;> simp [adj, eq_comm]

def compat {V : Type} (R : V → V → Prop) (z y : V → Bool) : Prop :=
  (∀ v, z v = false → y v = false) ∧
  ∀ i j, R i j → z i = true → z j = true → y i = true → y j = true

def covers {V : Type} (R : V → V → Prop) (z : V → Bool) (x : V × Bool → Bool) : Prop :=
  (∀ p q, adj R p q → x p = true ∨ x q = true) ∧
  ∀ i, xor (x (i,false)) (x (i,true)) = z i

lemma marked_model {V : Type} (R : V → V → Prop) (z : V → Bool)
    (x : V × Bool → Bool) (hx : covers R z x) :
    let y := fun v => z v && x (v,false)
    compat R z y ∧ ∀ v b, x (v,b) = tip (z v) (y v) b := by
  dsimp only
  have pair (v : V) := hx.1 (v,false) (v,true) (by simp [adj])
  have repr (v : V) (b : Bool) : x (v,b) = tip (z v) (z v && x (v,false)) b := by
    have h := pair v
    have hz := hx.2 v
    cases b <;> cases h₁ : x (v,false) <;> cases h₂ : x (v,true) <;>
      cases h₃ : z v <;> simp_all [tip]
  refine ⟨⟨fun v h => by simp [h], ?_⟩, repr⟩
  intro i j hij hi hj hy
  have h := hx.1 (i,true) (j,false) (by simp [adj, hij])
  rw [repr i true] at h
  simp only [hi, hj, Bool.true_and, tip, ite_true, Bool.not_eq_true'] at h ⊢
  grind

lemma model_marked {V : Type} (R : V → V → Prop) (z y : V → Bool)
    (hy : compat R z y) :
    covers R z (fun p => tip (z p.1) (y p.1) p.2) := by
  constructor
  · rintro ⟨i,a⟩ ⟨j,b⟩ hab
    have go (i j : V) (h : i = j ∨ R i j) :
        tip (z i) (y i) true = true ∨ tip (z j) (y j) false = true := by
      rcases h with rfl | hij
      · cases z i <;> cases y i <;> simp [tip]
      · have H := hy.2 i j hij
        cases e₁ : z i <;> cases e₂ : z j <;> cases e₃ : y i <;> cases e₄ : y j <;> simp_all [tip]
    cases a <;> cases b <;> simp [adj] at hab
    · exact (go j i (hab.imp_left Eq.symm)).symm
    · exact go i j hab
  · intro i
    change xor (tip (z i) (y i) false) (tip (z i) (y i) true) = z i
    cases z i <;> cases y i <;> rfl

lemma masked_tip (z y : Bool) (h : z = false → y = false) :
    (z && tip z y false) = y := by
  cases z <;> cases y <;> simp_all [tip]

noncomputable def relNB {V : Type} [Fintype V] (R : V → V → Prop) (p : V × Bool) :
    Finset (V × Bool) := by
  classical
  exact Finset.univ.filter (adj R p)

lemma mem_relNB {V : Type} [Fintype V] (R : V → V → Prop) (p q : V × Bool) :
    q ∈ relNB R p ↔ adj R p q := by classical simp [relNB]

def matching {V : Type} (R : V → V → Prop) : Prop :=
  (∀ i j k, R i j → R i k → j = k) ∧ (∀ i j k, R j i → R k i → j = k)

lemma neighbor_bound {V : Type} [Fintype V] (A B : V → V → Prop)
    (ha : matching A) (hb : matching B) (p : V × Bool) :
    (relNB (fun i j => A i j ∨ B i j) p).card ≤ 3 := by
  classical
  let side (R : V → V → Prop) := Finset.univ.filter (fun q : V × Bool =>
    p.2 ≠ q.2 ∧ if p.2 then R p.1 q.1 else R q.1 p.1)
  have one (R) (hm : matching R) : (side R).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨i,a⟩ hi ⟨j,b⟩ hj
    simp only [side, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    obtain ⟨v,c⟩ := p
    cases c <;> cases a <;> cases b <;> simp_all
    · exact hm.2 v i j hi hj
    · exact hm.1 v i j hi hj
  have sub : relNB (fun i j => A i j ∨ B i j) p ⊆
      insert (p.1, !p.2) (side A ∪ side B) := by
    rintro ⟨i,a⟩ hi
    rw [mem_relNB] at hi
    obtain ⟨v,c⟩ := p
    cases c <;> cases a <;> simp [adj] at hi <;> simp [side] <;> grind
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ ≤ (side A ∪ side B).card + 1 := Finset.card_insert_le ..
    _ ≤ 3 := by have := Finset.card_union_le (side A) (side B); have := one A ha; have := one B hb; omega

def ft {I O : Type} (owner : O → I) : I ⊕ O → I := Sum.elim id owner

def birth {I O : Type} (time : O → ℕ) : I ⊕ O → ℕ := Sum.elim (fun _ => 0) time

lemma front_ext {I O : Type} {owner : O → I} {time : O → ℕ}
    (hp : ∀ o, 0 < time o) (hu : ∀ a b, owner a = owner b → time a = time b → a = b)
    {f g : I ⊕ O} (h₁ : ft owner f = ft owner g) (h₂ : birth time f = birth time g) :
    f = g := by
  cases f with
  | inl i =>
    cases g with
    | inl j => exact congrArg Sum.inl h₁
    | inr b => change 0 = time b at h₂; have := hp b; omega
  | inr a =>
    cases g with
    | inl j => change time a = 0 at h₂; have := hp a; omega
    | inr b => exact congrArg Sum.inr (hu a b h₁ h₂)

lemma before_exists {I O : Type} [Fintype I] [Fintype O] (owner : O → I) (time : O → ℕ)
    (i : I) (t : ℕ) :
    ∃ f : I ⊕ O, ft owner f = i ∧ birth time f ≤ t ∧
      ∀ g, ft owner g = i → birth time g ≤ t → birth time g ≤ birth time f := by
  classical
  let s := Finset.univ.filter (fun g : I ⊕ O => ft owner g = i ∧ birth time g ≤ t)
  have h : Sum.inl i ∈ s := by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, Nat.zero_le _⟩
  obtain ⟨f, hf, hmax⟩ := s.exists_max_image (birth time) ⟨_, h⟩
  simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hf hmax
  exact ⟨f, hf.1, hf.2, fun g hg ht => hmax g ⟨hg, ht⟩⟩

noncomputable def before {I O : Type} [Fintype I] [Fintype O] (owner : O → I) (time : O → ℕ)
    (i : I) (t : ℕ) := Classical.choose (before_exists owner time i t)

lemma before_spec {I O : Type} [Fintype I] [Fintype O] (owner : O → I) (time : O → ℕ)
    (i : I) (t : ℕ) :
    ft owner (before owner time i t) = i ∧ birth time (before owner time i t) ≤ t ∧
      ∀ g, ft owner g = i → birth time g ≤ t → birth time g ≤ birth time (before owner time i t) :=
  Classical.choose_spec (before_exists owner time i t)

noncomputable def prev {I O : Type} [Fintype I] [Fintype O] (owner : O → I) (time : O → ℕ) (o : O) :=
  before owner time (owner o) (time o - 1)

lemma prev_inj {I O : Type} [Fintype I] [Fintype O] {owner : O → I} {time : O → ℕ}
    (hp : ∀ o, 0 < time o) (hu : ∀ a b, owner a = owner b → time a = time b → a = b) :
    Function.Injective (prev owner time) := by
  intro a b he
  have ha := before_spec owner time (owner a) (time a - 1)
  have hb := before_spec owner time (owner b) (time b - 1)
  unfold prev at he
  rw [he] at ha
  have ho := ha.1.symm.trans hb.1
  apply hu a b ho
  have lt (x y : O) (h : owner x = owner y) (ht : time x < time y) :
      time x ≤ birth time (before owner time (owner y) (time y - 1)) := by
    exact (before_spec owner time _ _).2.2 (Sum.inr x) h (by change time x ≤ time y - 1; omega)
  have pa := hp a
  have pb := hp b
  have H₁ := lt a b ho
  have H₂ := lt b a ho.symm
  rw [he] at H₂
  obtain ⟨_, h₁, _⟩ := ha
  obtain ⟨_, h₂, _⟩ := hb
  omega

abbrev Vtx (I O : Type) := (I ⊕ O) ⊕ O

def tagV {I O : Type} (owner : O → I) : Vtx I O → I := Sum.elim (ft owner) owner

def layerA {I O : Type} (pr : O → I ⊕ O) : Vtx I O → Vtx I O → Prop
  | .inl f, .inr o => f = pr o
  | .inr o, .inl g => g = .inr o
  | _, _ => False

def layerB {I E : Type} (pr : E × Bool → I ⊕ (E × Bool)) :
    Vtx I (E × Bool) → Vtx I (E × Bool) → Prop
  | .inl (.inr o), .inl g => g = pr o
  | .inr a, .inr b => a.1 = b.1 ∧ a.2 = false ∧ b.2 = true
  | _, _ => False

lemma layerA_match {I O : Type} {pr : O → I ⊕ O} (h : Function.Injective pr) :
    matching (layerA pr) := by
  constructor <;> intro i j k hj hk <;>
    cases i <;> cases j <;> cases k <;> simp_all [layerA]; grind [Function.Injective]

lemma layerB_match {I E : Type} {pr : E × Bool → I ⊕ (E × Bool)} (h : Function.Injective pr) :
    matching (layerB pr) := by
  constructor <;> intro i j k hj hk <;>
    rcases i with (i|i)|⟨i,a⟩ <;> rcases j with (j|j)|⟨j,b⟩ <;>
    rcases k with (k|k)|⟨k,c⟩ <;> simp_all [layerB] <;> grind [Function.Injective]

def wire {I E : Type} (pr : E × Bool → I ⊕ (E × Bool)) (v w : Vtx I (E × Bool)) : Prop :=
  layerA pr v w ∨ layerB pr v w

lemma ring_eq {I E : Type} (owner : E × Bool → I) (pr : E × Bool → I ⊕ (E × Bool))
    (htag : ∀ o, ft owner (pr o) = owner o)
    (z : I → Bool) (b : Vtx I (E × Bool) → Bool)
    (hb : compat (wire pr) (fun v => z (tagV owner v)) b) (o : E × Bool) :
    b (.inr o) = b (.inl (pr o)) ∧ b (.inl (.inr o)) = b (.inl (pr o)) := by
  let f : Vtx I (E × Bool) := .inl (pr o)
  let p : Vtx I (E × Bool) := .inr o
  let g : Vtx I (E × Bool) := .inl (.inr o)
  have hf : tagV owner f = owner o := htag o
  have hp : tagV owner p = owner o := rfl
  have hg : tagV owner g = owner o := rfl
  have h₁ := hb.2 f p (Or.inl (show layerA pr f p from rfl))
  have h₂ := hb.2 p g (Or.inl (show layerA pr p g from rfl))
  have h₃ := hb.2 g f (Or.inr (show layerB pr g f from rfl))
  have d₁ := hb.1 f
  have d₂ := hb.1 p
  have d₃ := hb.1 g
  change b p = b f ∧ b g = b f
  dsimp only at h₁ h₂ h₃ d₁ d₂ d₃
  rw [hf, hp] at h₁
  rw [hp, hg] at h₂
  rw [hg, hf] at h₃
  rw [hf] at d₁
  rw [hp] at d₂
  rw [hg] at d₃
  cases e₁ : z (owner o) <;> cases e₂ : b p <;> cases e₃ : b f <;> cases e₄ : b g <;> simp_all

def rootV {I O : Type} (i : I) : Vtx I O := .inl (.inl i)

lemma copied {I E : Type} [Fintype I] [Fintype E] (owner : E × Bool → I) (time : E × Bool → ℕ)
    (hp : ∀ o, 0 < time o) (z : I → Bool) (b : Vtx I (E × Bool) → Bool)
    (hb : compat (wire (prev owner time)) (fun v => z (tagV owner v)) b) :
    ∀ v, b v = b (rootV (tagV owner v)) := by
  let pr := prev owner time
  have spec (o) := before_spec owner time (owner o) (time o - 1)
  have ht (o) : ft owner (pr o) = owner o := (spec o).1
  have ring (o) := ring_eq owner pr ht z b hb o
  have front (f : I ⊕ (E × Bool)) : b (.inl f) = b (rootV (ft owner f)) := by
    induction hn : birth time f using Nat.strong_induction_on generalizing f with
    | ind n ih =>
      cases f with
      | inl i => rfl
      | inr o =>
        have hlt : birth time (pr o) < n := by
          change time o = n at hn
          have hle : birth time (pr o) ≤ time o - 1 := (spec o).2.1
          have := hp o
          omega
        exact (ring o).2.trans ((ih _ hlt (pr o) rfl).trans (congrArg (fun i => b (rootV i)) (ht o)))
  rintro (f|o)
  · exact front f
  · exact (ring o).1.trans ((front (pr o)).trans (congrArg (fun i => b (rootV i)) (ht o)))

lemma wire_tag {I E : Type} (owner : E × Bool → I) (pr : E × Bool → I ⊕ (E × Bool))
    (ht : ∀ o, ft owner (pr o) = owner o) (a b : Vtx I (E × Bool)) (h : wire pr a b) :
    tagV owner a = tagV owner b ∨
    ∃ e, tagV owner a = owner (e,false) ∧ tagV owner b = owner (e,true) := by
  rcases a with (i|o)|⟨e,c⟩ <;> rcases b with (j|u)|⟨d,k⟩ <;>
    simp only [wire, layerA, layerB, false_or, or_false] at h <;> try contradiction
  all_goals first
    | exact Or.inl (h ▸ ht _)
    | exact Or.inl (h ▸ (ht _).symm)
    | obtain ⟨rfl,rfl,rfl⟩ := h; exact Or.inr ⟨_,rfl,rfl⟩
    | cases h; exact Or.inl rfl

lemma semantics {I E W : Type} [Fintype I] [Fintype E]
    (owner : E × Bool → I) (time : E × Bool → ℕ) (hp : ∀ o, 0 < time o)
    (e : Vtx I (E × Bool) ≃ W) (D : I → I → Prop)
    (hD : ∀ i j, D i j ↔ ∃ d, owner (d,false) = i ∧ owner (d,true) = j)
    (z : I → Bool) :
    let tag := fun w => tagV owner (e.symm w)
    let rd := fun i => e (rootV i)
    let R := fun a b => wire (prev owner time) (e.symm a) (e.symm b)
    let read := fun (x : W × Bool → Bool) i => z i && x (rd i,false)
    (∀ x, covers R (fun w => z (tag w)) x → compat D z (read x)) ∧
    ∀ y, compat D z y → ∃! x, covers R (fun w => z (tag w)) x ∧ read x = y := by
  intro tag rd R read
  let pr := prev owner time
  have ht (o) : ft owner (pr o) = owner o := (before_spec owner time _ _).1
  have hrd (i) : tag (rd i) = i := by simp [tag, rd, rootV, tagV, ft]
  have project (x : W × Bool → Bool) (hx : covers R (fun w => z (tag w)) x) :
      compat D z (read x) ∧ ∀ w a, x (w,a) = tip (z (tag w)) (read x (tag w)) a := by
    let b := fun w => z (tag w) && x (w,false)
    obtain ⟨hb, hrepr⟩ := marked_model R _ x hx
    change compat R (fun w => z (tag w)) b at hb
    have pull : compat (wire pr) (fun v => z (tagV owner v)) (fun v => b (e v)) := by
      constructor
      · intro v hv
        apply hb.1
        simpa [tag] using hv
      · intro v u hv hz hz' hv'
        apply hb.2 (e v) (e u) _ _ _ hv'
        · simpa [R, pr] using hv
        · simpa [tag] using hz
        · simpa [tag] using hz'
    have cp (w) : b w = read x (tag w) := by
      have hh := copied owner time hp z (fun v => b (e v)) pull (e.symm w)
      simpa [b, read, rd, tag, rootV, tagV, ft] using hh
    refine ⟨⟨fun i hi => by simp [read, hi], ?_⟩, fun w a =>
      (hrepr w a).trans (congrArg (fun k => tip (z (tag w)) k a) (cp w))⟩
    intro i j hij hi hj hy
    obtain ⟨d,rfl,rfl⟩ := (hD i j).mp hij
    let p : Vtx I (E × Bool) := .inr (d,false)
    let q : Vtx I (E × Bool) := .inr (d,true)
    have arc : wire pr p q := Or.inr ⟨rfl,rfl,rfl⟩
    have h₁ : tag (e p) = owner (d,false) := by simp [tag, p, tagV]
    have h₂ : tag (e q) = owner (d,true) := by simp [tag, q, tagV]
    have HH := pull.2 p q arc hi hj
    dsimp only at HH
    rw [cp (e p), cp (e q), h₁, h₂] at HH
    exact HH hy
  refine ⟨fun x hx => (project x hx).1, ?_⟩
  intro y hy
  let x := fun (p : W × Bool) => tip (z (tag p.1)) (y (tag p.1)) p.2
  have extend : compat R (fun w => z (tag w)) (fun w => y (tag w)) := by
    constructor
    · exact fun w => hy.1 _
    · intro a b hab hz hz' ha
      obtain eq | ⟨d,h₁,h₂⟩ := wire_tag owner pr ht (e.symm a) (e.symm b) hab
      · change tag a = tag b at eq
        simpa only [← eq] using ha
      · exact hy.2 _ _ ((hD _ _).mpr ⟨d,h₁.symm,h₂.symm⟩) hz hz' ha
  refine ⟨x, ⟨model_marked R _ _ extend, ?_⟩, ?_⟩
  · funext i
    dsimp only [read, x]
    rw [hrd]
    exact masked_tip _ _ (hy.1 i)
  · rintro x' ⟨hx',hread⟩
    funext ⟨w,a⟩
    simpa only [hread] using (project x' hx').2 w a

def active {I O : Type} (owner : O → I) (time : O → ℕ) (f : I ⊕ O) (t : ℕ) : Prop :=
  birth time f ≤ t ∧ ∀ g, ft owner g = ft owner f → birth time f < birth time g → t ≤ birth time g

def present {I O : Type} (owner : O → I) (time : O → ℕ) (live : ℕ → Finset I)
    (t : ℕ) : Vtx I O → Prop
  | .inl f => ft owner f ∈ live t ∧ active owner time f t
  | .inr o => time o = t

noncomputable def pathBag {I O : Type} [Fintype I] [Fintype O] (owner : O → I) (time : O → ℕ)
    (live : ℕ → Finset I) (t : ℕ) : Finset (Vtx I O) := by
  classical
  exact Finset.univ.filter (present owner time live t)

lemma mem_pathBag {I O : Type} [Fintype I] [Fintype O] (owner : O → I) (time : O → ℕ)
    (live : ℕ → Finset I) (t : ℕ) (v : Vtx I O) :
    v ∈ pathBag owner time live t ↔ present owner time live t v := by classical simp [pathBag]

lemma present_interval {I O : Type} (owner : O → I) (time : O → ℕ) (live : ℕ → Finset I)
    {s t u : ℕ} (hst : s ≤ t) (htu : t ≤ u)
    (hc : ∀ i, i ∈ live s → i ∈ live u → i ∈ live t)
    (v : Vtx I O) (hs : present owner time live s v) (hu : present owner time live u v) :
    present owner time live t v := by
  cases v with
  | inl f => exact ⟨hc _ hs.1 hu.1, hs.2.1.trans hst, fun g h h' => htu.trans (hu.2.2 g h h')⟩
  | inr o => change time o = s at hs; change time o = u at hu; change time o = t; omega

lemma triangle_present {I O : Type} [Fintype I] [Fintype O] (owner : O → I) (time : O → ℕ)
    (live : ℕ → Finset I) (o : O) (hp : 0 < time o) (ho : owner o ∈ live (time o)) :
    present owner time live (time o) (.inl (prev owner time o)) ∧
    present owner time live (time o) (.inr o) ∧
    present owner time live (time o) (.inl (.inr o)) := by
  obtain ⟨ht,hle,hm⟩ := before_spec owner time (owner o) (time o - 1)
  refine ⟨⟨ht ▸ ho, hle.trans (Nat.sub_le ..), ?_⟩, rfl, ⟨ho, le_rfl, ?_⟩⟩
  · intro g hg hlt
    rw [show ft owner (prev owner time o) = owner o from ht] at hg
    by_contra! hn
    exact (not_le_of_gt hlt) (hm g hg (by omega))
  · intro g _ hlt
    exact le_of_lt hlt

lemma root_present {I O : Type} [Fintype I] [Fintype O] (owner : O → I) (time : O → ℕ)
    (live : ℕ → Finset I) (S : Finset ℕ) (events : ∀ o, time o ∈ S ∧ owner o ∈ live (time o))
    (i : I) (hi : ∃ t ∈ S, i ∈ live t) :
    ∃ t ∈ S, present owner time live t (rootV i) := by
  classical
  let os := Finset.univ.filter (fun o => owner o = i)
  by_cases h : os.Nonempty
  · obtain ⟨o,ho,hm⟩ := os.exists_min_image time h
    have heq : owner o = i := (Finset.mem_filter.mp ho).2
    refine ⟨time o,(events o).1, heq ▸ (events o).2, Nat.zero_le _, ?_⟩
    rintro (j|a) ha hlt
    · exact False.elim ((Nat.lt_irrefl 0) hlt)
    · exact hm a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
  · obtain ⟨t,ht,hv⟩ := hi
    refine ⟨t,ht,hv,Nat.zero_le _,?_⟩
    rintro (j|a) ha hlt
    · exact False.elim ((Nat.lt_irrefl 0) hlt)
    · exact False.elim (h ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩)

lemma wire_present {I E : Type} [Fintype I] [Fintype E] (owner : E × Bool → I) (clock : E → ℕ)
    (live : ℕ → Finset I) (S : Finset ℕ) (hp : ∀ e, 0 < clock e)
    (events : ∀ o : E × Bool, clock o.1 ∈ S ∧ owner o ∈ live (clock o.1))
    (v w : Vtx I (E × Bool))
    (h : wire (prev owner (fun o => clock o.1)) v w) :
    ∃ t ∈ S, present owner (fun o => clock o.1) live t v ∧ present owner (fun o => clock o.1) live t w := by
  let time := fun (o : E × Bool) => clock o.1
  let pr := prev owner time
  have tri (o) := triangle_present owner time live o (hp o.1) (events o).2
  cases v with
  | inl f =>
    cases w with
    | inr o =>
      have eq : f = pr o := by simpa [wire,layerA,layerB] using h
      exact ⟨_,(events o).1,eq ▸ (tri o).1,(tri o).2.1⟩
    | inl g =>
      cases f with
      | inl i => simp [wire,layerA,layerB] at h
      | inr o =>
        have eq : g = pr o := by simpa [wire,layerA,layerB] using h
        exact ⟨_,(events o).1,(tri o).2.2,eq ▸ (tri o).1⟩
  | inr o =>
    cases w with
    | inl g =>
      have eq : g = Sum.inr o := by simpa [wire,layerA,layerB] using h
      exact ⟨_,(events o).1,(tri o).2.1,eq ▸ (tri o).2.2⟩
    | inr b =>
      have eq : o.1 = b.1 := (show o.1 = b.1 ∧ _ from (by simpa [wire,layerA,layerB] using h)).1
      exact ⟨_,(events o).1,rfl,congrArg clock eq.symm⟩

lemma pathBag_card {I E : Type} [Fintype I] [Fintype E] (owner : E × Bool → I)
    (clock : E → ℕ) (hp : ∀ e, 0 < clock e) (hclock : Function.Injective clock)
    (hu : ∀ a b : E × Bool, owner a = owner b → clock a.1 = clock b.1 → a = b)
    (live : ℕ → Finset I) (t : ℕ) (ht : 0 < t) :
    (pathBag owner (fun o => clock o.1) live t).card ≤ (live t).card + 4 := by
  classical
  let time := fun (o : E × Bool) => clock o.1
  let core := (live t).image (fun i => (Sum.inl (before owner time i (t-1)) : Vtx I (E × Bool)))
  have hcore : core.card ≤ (live t).card := Finset.card_image_le
  have classify (v) (hv : v ∈ pathBag owner time live t) :
      v ∈ core ∨ ∃ o, clock o.1 = t ∧ (v = Sum.inr o ∨ v = Sum.inl (Sum.inr o)) := by
    rw [mem_pathBag] at hv
    cases v with
    | inr o => exact Or.inr ⟨o,hv,Or.inl rfl⟩
    | inl f =>
      obtain ⟨hlive,hborn,hmax⟩ := hv
      by_cases he : birth time f = t
      · cases f with
        | inl i => change 0 = t at he; omega
        | inr o => exact Or.inr ⟨o,he,Or.inr rfl⟩
      · left
        obtain ⟨htag,hb,hm⟩ := before_spec owner time (ft owner f) (t-1)
        apply Finset.mem_image.mpr
        refine ⟨ft owner f, hlive, congrArg Sum.inl (front_ext (fun o => hp o.1) hu htag ?_)⟩
        apply le_antisymm _ (hm f rfl (by omega))
        by_contra! hlt
        have := hmax _ htag hlt
        omega
  by_cases hex : ∃ e, clock e = t
  · obtain ⟨e,he⟩ := hex
    let a : E × Bool := (e,false)
    let b : E × Bool := (e,true)
    let extra : Finset (Vtx I (E × Bool)) := {.inr a,.inr b,.inl (.inr a),.inl (.inr b)}
    have sub : pathBag owner time live t ⊆ core ∪ extra := by
      intro v hv
      apply Finset.mem_union.mpr
      rcases classify v hv with hc | ⟨⟨d,k⟩,hd,hv'⟩
      · exact Or.inl hc
      · have hh : d = e := hclock (hd.trans he.symm)
        subst d
        right
        cases k <;> rcases hv' with rfl | rfl <;> simp [extra,a,b]
    have hbound : extra.card ≤ 4 := by
      have h₁ := Finset.card_insert_le (Sum.inr a : Vtx I (E × Bool)) {Sum.inr b, Sum.inl (Sum.inr a), Sum.inl (Sum.inr b)}
      have h₂ := Finset.card_insert_le (Sum.inr b : Vtx I (E × Bool)) {Sum.inl (Sum.inr a), Sum.inl (Sum.inr b)}
      have h₃ := Finset.card_insert_le (Sum.inl (Sum.inr a) : Vtx I (E × Bool)) {Sum.inl (Sum.inr b)}
      simp only [Finset.card_singleton] at h₃
      dsimp only [extra]
      omega
    exact (Finset.card_le_card sub).trans ((Finset.card_union_le ..).trans (Nat.add_le_add hcore hbound))
  · have sub : pathBag owner time live t ⊆ core := by
      intro v hv
      rcases classify v hv with hv | ⟨o,he,_⟩
      · exact hv
      · exact False.elim (hex ⟨o.1,he⟩)
    exact (Finset.card_le_card sub).trans (by omega)

lemma schedule {I E : Type} [Fintype E] {l w : ℕ} (bag : Fin l → Finset I)
    (bound : ∀ j, (bag j).card ≤ w) (allV : ∀ i, ∃ j, i ∈ bag j)
    (interval : ∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t)
    (owner : E × Bool → I) (site : E → Fin l) (atSite : ∀ o : E × Bool, owner o ∈ bag (site o.1)) :
    ∃ (clock : E → ℕ) (S : Finset ℕ) (live : ℕ → Finset I),
      Function.Injective clock ∧ (∀ e, 0 < clock e) ∧ S.card ≤ l + Fintype.card E ∧
      (∀ t ∈ S, 0 < t ∧ (live t).card ≤ w) ∧
      (∀ i, ∃ t ∈ S, i ∈ live t) ∧ (∀ o : E × Bool, clock o.1 ∈ S ∧ owner o ∈ live (clock o.1)) ∧
      ∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ S, s ≤ t → t ≤ u → ∀ i, i ∈ live s → i ∈ live u → i ∈ live t := by
  classical
  let N := Fintype.card E
  let idx := Fintype.equivFin E
  let stamp (j : Fin l) (k : ℕ) := k + j.val * (N+1) + 1
  let block (t : ℕ) := (t-1) / (N+1)
  let first (j : Fin l) := stamp j 0
  let offset (e : E) := (idx e).val + 1
  let clock (e : E) := stamp (site e) (offset e)
  let S := Finset.univ.image first ∪ Finset.univ.image clock
  let live (t : ℕ) := if h : block t < l then bag ⟨block t,h⟩ else ∅
  have small (e : E) : offset e < N+1 := Nat.succ_lt_succ (idx e).isLt
  have block_eq (j k) (hk : k < N+1) : block (stamp j k) = j.val := by
    simp [block,stamp,Nat.add_mul_div_right _ _ (Nat.succ_pos N),Nat.div_eq_of_lt hk]
  have live_eq (j k) (hk : k < N+1) : live (stamp j k) = bag j := by
    simp [live,block_eq j k hk]
  have incl (e : E) : clock e ∈ S :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))
  have valid (t) (ht : t ∈ S) : 0 < t ∧ block t < l := by
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨Nat.succ_pos _, (block_eq j 0 (Nat.succ_pos N)) ▸ j.isLt⟩
    · obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨Nat.succ_pos _, (block_eq (site e) _ (small e)) ▸ (site e).isLt⟩
  refine ⟨clock,S,live,?_,fun _ => Nat.succ_pos _,?_,?_,?_,?_,?_⟩
  · intro a b h
    have remEq := congrArg (fun t => (t-1) % (N+1)) h
    simp only [clock,stamp,Nat.add_sub_cancel,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (small _)] at remEq
    exact idx.injective (Fin.ext (Nat.succ.inj remEq))
  · have h₁ := Finset.card_image_le (f := first) (s := Finset.univ)
    have h₂ := Finset.card_image_le (f := clock) (s := Finset.univ)
    simpa [S] using (Finset.card_union_le _ _).trans (Nat.add_le_add h₁ h₂)
  · intro t ht
    exact ⟨(valid t ht).1, by simpa [live,(valid t ht).2] using bound ⟨_,(valid t ht).2⟩⟩
  · intro i
    obtain ⟨j,hj⟩ := allV i
    refine ⟨first j,Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)),?_⟩
    simpa only [first, live_eq j 0 (Nat.succ_pos N)] using hj
  · intro o
    exact ⟨incl _, by simpa only [clock,live_eq (site o.1) _ (small o.1)] using atSite o⟩
  · intro s hs t ht u hu hst htu i hi hj
    have mono : Monotone block := fun a b hab => Nat.div_le_div_right (Nat.sub_le_sub_right hab 1)
    simp only [live,dite_eq_left (valid s hs).2,dite_eq_left (valid t ht).2,dite_eq_left (valid u hu).2] at hi hj ⊢
    exact interval i _ _ _ (mono hst) (mono htu) hi hj

lemma matching_pull {W V : Type} {R : V → V → Prop} (f : W → V) (hf : Function.Injective f)
    (hm : matching R) : matching (fun a b => R (f a) (f b)) :=
  ⟨fun i j k h h' => hf (hm.1 (f i) (f j) (f k) h h'),
   fun i j k h h' => hf (hm.2 (f i) (f j) (f k) h h')⟩

lemma physical_iff {W : Type} [Fintype W] (R : W → W → Prop) (z : W → Bool)
    (x : W × Bool → Bool) :
    ((∀ p, ∀ q ∈ relNB R p, x p = true ∨ x q = true) ∧
      ∀ i, xor (x (i,false)) (x (i,true)) = z i) ↔ covers R z x := by
  simp only [covers,mem_relNB]

lemma undirected_arc {W : Type} [Fintype W] (R : W → W → Prop) {i j : W}
    (h : i ≠ j ∧ ∃ a b : Bool, (j,b) ∈ relNB R (i,a)) : R i j ∨ R j i := by
  obtain ⟨hne,a,b,hm⟩ := h
  have ha := ((mem_relNB ..).mp hm).2
  cases a <;> simp_all

lemma build_path {I E W : Type} [Fintype I] [Fintype E] [Fintype W]
    (owner : E × Bool → I) (clock : E → ℕ) (e : Vtx I (E × Bool) ≃ W)
    (S : Finset ℕ) (live : ℕ → Finset I) (w : ℕ)
    (hc : Function.Injective clock) (hp : ∀ d, 0 < clock d)
    (hu : ∀ a b : E × Bool, owner a = owner b → clock a.1 = clock b.1 → a = b)
    (width : ∀ t ∈ S, 0 < t ∧ (live t).card ≤ w)
    (allV : ∀ i, ∃ t ∈ S, i ∈ live t)
    (events : ∀ o : E × Bool, clock o.1 ∈ S ∧ owner o ∈ live (clock o.1))
    (interval : ∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ S, s ≤ t → t ≤ u →
      ∀ i, i ∈ live s → i ∈ live u → i ∈ live t) :
    let R := fun a b => wire (prev owner (fun o => clock o.1)) (e.symm a) (e.symm b)
    ∃ bag : Fin S.card → Finset W,
      (∀ t, (bag t).card ≤ w+6) ∧
      (∀ i, ∃ t, i ∈ bag t) ∧
      (∀ i j, (i ≠ j ∧ ∃ a b : Bool, (j,b) ∈ relNB R (i,a)) → ∃ t, i ∈ bag t ∧ j ∈ bag t) ∧
      ∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t := by
  intro R
  classical
  let time := fun (o : E × Bool) => clock o.1
  let seq := S.orderIsoOfFin rfl
  let bag (j : Fin S.card) := (pathBag owner time live (seq j).val).map e.toEmbedding
  have mem (j i) : i ∈ bag j ↔ present owner time live (seq j).val (e.symm i) := by
    rw [show bag j = _ from rfl, Finset.mem_map_equiv,mem_pathBag]
  have idx (t) (ht : t ∈ S) : ∃ j, (seq j).val = t := by
    exact ⟨seq.symm ⟨t,ht⟩,congrArg Subtype.val (seq.apply_symm_apply ⟨t,ht⟩)⟩
  refine ⟨bag,?_,?_,?_,?_⟩
  · intro j
    have hh := width _ (seq j).property
    have hc' := pathBag_card owner clock hp hc hu live _ hh.1
    have hw := hh.2
    simp only [bag,Finset.card_map]
    change (pathBag owner (fun o => clock o.1) live (seq j).val).card ≤ w + 6
    omega
  · intro i
    have witness (v : Vtx I (E × Bool)) : ∃ t ∈ S, present owner time live t v := by
      rcases v with (j|o)|o
      · exact root_present owner time live S events j (allV j)
      · exact ⟨_,(events o).1,(triangle_present owner time live o (hp o.1) (events o).2).2.2⟩
      · exact ⟨_,(events o).1,rfl⟩
    obtain ⟨t,ht,hi⟩ := witness (e.symm i)
    obtain ⟨j,hj⟩ := idx t ht
    exact ⟨j,(mem ..).mpr (hj ▸ hi)⟩
  · intro i j hij
    have both (i j : W) (hr : R i j) : ∃ k, i ∈ bag k ∧ j ∈ bag k := by
      obtain ⟨t,ht,hi,hj⟩ := wire_present owner clock live S hp events _ _ hr
      obtain ⟨k,hk⟩ := idx t ht
      exact ⟨k,(mem ..).mpr (hk ▸ hi),(mem ..).mpr (hk ▸ hj)⟩
    rcases undirected_arc R hij with h | h
    · exact both i j h
    · obtain ⟨k,hj,hi⟩ := both _ _ h
      exact ⟨k,hi,hj⟩
  · intro i s t u hst htu hs hu'
    have h₁ : (seq s).val ≤ (seq t).val := seq.monotone hst
    have h₂ : (seq t).val ≤ (seq u).val := seq.monotone htu
    exact (mem ..).mpr (present_interval owner time live h₁ h₂
      (interval _ (seq s).property _ (seq t).property _ (seq u).property h₁ h₂)
      _ ((mem ..).mp hs) ((mem ..).mp hu'))

end PEqualNP.Outside.L_lib_1205_aux

open PEqualNP.Outside.L_lib_1205_aux

theorem PEqualNP.Outside.L_lib_1205 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
let bags := fun (v : Nat) (edge : Fin v → Fin v → Prop) (w : Nat) =>
  ∃ (l : Nat) (bag : Fin l → Finset (Fin v)),
    l ≤ 2*v+1 ∧ (∀ t, (bag t).card ≤ w) ∧
    (∀ i, ∃ t, i ∈ bag t) ∧
    (∀ i j, edge i j → ∃ t, i ∈ bag t ∧ j ∈ bag t) ∧
    ∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t
∀ (n w : Nat) (D : Finset (Fin n × Fin n)), (∀ i, (i,i) ∉ D) →
  bags n (fun i j => (i,j) ∈ D) w →
  ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (tag : Fin m → Fin n) (rd : Fin n → Fin m),
    m ≤ n+6*D.card ∧ (∀ i, tag (rd i) = i) ∧
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
    (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧ (∀ p, ∀ q ∈ nb p, p.2 ≠ q.2) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    bags m (fun i j => i ≠ j ∧ ∃ a b : Bool, (j,b) ∈ nb (i,a)) (w+6) ∧
    ∀ z : Fin n → Bool,
      let physical := fun (x : (Fin m × Bool) → Bool) =>
        (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
        ∀ i, xor (x (i,false)) (x (i,true)) = z (tag i)
      let legal := fun (y : Fin n → Bool) =>
        (∀ i, z i = false → y i = false) ∧
        ∀ i j, (i,j) ∈ D → z i = true → z j = true → y i = true → y j = true
      let readout := fun (x : (Fin m × Bool) → Bool) i => z i && x (rd i,false)
      (∀ x, physical x → legal (readout x)) ∧
      ∀ y, legal y → ∃! x, physical x ∧ readout x = y) := by
  classical
  dsimp only
  intro n w D noLoop hb
  obtain ⟨l,bag,hlen,hwidth,hall,hedge,hinterval⟩ := hb
  let owner (o : ↥D × Bool) := if o.2 then o.1.val.2 else o.1.val.1
  have both (d : ↥D) := hedge d.val.1 d.val.2 d.property
  let site (d : ↥D) := Classical.choose (both d)
  have atSite (o : ↥D × Bool) : owner o ∈ bag (site o.1) := by
    obtain ⟨d,b⟩ := o
    have hh := Classical.choose_spec (both d)
    cases b
    · exact hh.1
    · exact hh.2
  obtain ⟨clock,S,live,hc,hp,hlen',width,allV,events,interval⟩ :=
    schedule bag hwidth hall hinterval owner site atSite
  let time (o : ↥D × Bool) := clock o.1
  have hu (a b : ↥D × Bool) (ho : owner a = owner b) (ht : time a = time b) : a = b := by
    obtain ⟨d,i⟩ := a
    obtain ⟨d',j⟩ := b
    have he : d = d' := hc ht
    subst d'
    have hn : d.val.1 ≠ d.val.2 := by
      intro heq
      have hm := d.property
      rcases d with ⟨⟨u,v⟩, hmem⟩
      change u = v at heq
      subst v
      exact noLoop u hmem
    cases i <;> cases j <;> simp_all [owner]
  have hD (i j : Fin n) : (i,j) ∈ D ↔ ∃ d, owner (d,false) = i ∧ owner (d,true) = j := by
    constructor
    · intro h
      exact ⟨⟨(i,j),h⟩,rfl,rfl⟩
    · rintro ⟨⟨⟨a,b⟩,hab⟩,rfl,rfl⟩
      exact hab
  let pr := prev owner time
  let m := Fintype.card (Vtx (Fin n) (↥D × Bool))
  let e : Vtx (Fin n) (↥D × Bool) ≃ Fin m := Fintype.equivFin _
  let tag (j : Fin m) := tagV owner (e.symm j)
  let rd (i : Fin n) := e (rootV i)
  let R (i j : Fin m) := wire pr (e.symm i) (e.symm j)
  have hm : m = n + 4 * D.card := by
    simp [m,Fintype.card_prod,Fintype.card_sum]
    omega
  have hmA := matching_pull e.symm e.symm.injective (layerA_match (prev_inj (fun o => hp o.1) hu))
  have hmB := matching_pull e.symm e.symm.injective (layerB_match (prev_inj (fun o => hp o.1) hu))
  refine ⟨m,relNB R,tag,rd,by omega,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    simp [tag,rd,tagV,rootV,ft]
  · intro p
    exact ⟨fun h => ((mem_relNB R p p).mp h).1 rfl,neighbor_bound _ _ hmA hmB p⟩
  · intro p q
    simp only [mem_relNB,adj_comm R p q]
  · intro p q h
    exact ((mem_relNB R p q).mp h).1
  · intro i
    exact (mem_relNB ..).mpr ⟨Bool.false_ne_true,Or.inl rfl⟩
  · obtain ⟨bags,hs⟩ := build_path owner clock e S live w hc hp hu width allV events interval
    have hcard : Fintype.card ↥D = D.card := Fintype.card_coe _
    exact ⟨S.card,bags,by omega,hs⟩
  · intro z
    have hs := semantics owner time (fun o => hp o.1) e (fun i j => (i,j) ∈ D) hD z
    simpa only [← physical_iff,compat] using hs
