import Mathlib
import PEqualNP.Defs

open scoped BigOperators
namespace PEqualNP.Outside.L_lib_990

namespace QL990

abbrev F := ZMod 2
abbrev S (k : ℕ) := Fin k → F

def Quad {k : ℕ} (f : S k → F) : Prop :=
  ∃ (b : F) (l : S k) (M : Fin k → Fin k → F),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j

noncomputable def Rel {k : ℕ} (E : Finset (S k)) : Finset (Finset (S k)) :=
  E.powerset.filter (fun U => @decide
    (∀ f : S k → F, Quad f → (∑ s ∈ U, f s) = 0) (Classical.propDecidable _))

def triple {k : ℕ} (a b c s : S k) : F := dotProduct a s * dotProduct b s * dotProduct c s

def Fit {k : ℕ} (E : Finset (S k)) (a b : S k) (h : S k → F) : Prop :=
  ∃ (c : S k) (f : S k → F), Quad f ∧ ∀ s ∈ E, h s = f s + triple a b c s

def Good {k : ℕ} (E : Finset (S k)) (a b : S k) : Prop := ∀ h : S k → F, Fit E a b h

lemma field_cases (x : F) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

lemma mem_rel {k : ℕ} {E U : Finset (S k)} :
    U ∈ Rel E ↔ U ⊆ E ∧ ∀ f : S k → F, Quad f → ∑ s ∈ U, f s = 0 := by
  classical
  simp [Rel]

lemma quad_zero {k : ℕ} : Quad (0 : S k → F) := ⟨0, 0, 0, by simp⟩

lemma quad_add {k : ℕ} {f g : S k → F} (hf : Quad f) (hg : Quad g) : Quad (f + g) := by
  obtain ⟨bf, lf, Mf, hf⟩ := hf
  obtain ⟨bg, lg, Mg, hg⟩ := hg
  refine ⟨bf + bg, lf + lg, Mf + Mg, fun s => ?_⟩
  simp only [Pi.add_apply, hf s, hg s, add_dotProduct, add_mul, Finset.sum_add_distrib]
  abel

lemma triple_add {k : ℕ} (a b c d s : S k) :
    triple a b (c + d) s = triple a b c s + triple a b d s := by
  simp [triple, mul_add]

noncomputable def fits {k : ℕ} (E : Finset (S k)) (a b : S k) : Submodule F (E → F) := by
  refine { carrier := { h | ∃ (c : S k) (f : S k → F), Quad f ∧ ∀ s : E, h s = f s + triple a b c s },
           zero_mem' := ⟨0, 0, quad_zero, by simp [triple]⟩, add_mem' := ?_, smul_mem' := ?_ }
  · rintro u v ⟨c, f, hf, hu⟩ ⟨d, g, hg, hv⟩
    refine ⟨c + d, f + g, quad_add hf hg, fun s => ?_⟩
    simp only [Pi.add_apply, hu s, hv s, triple_add]
    abel
  · intro r u hu
    rcases field_cases r with rfl | rfl
    · simpa only [zero_smul] using (show (0 : E → F) ∈ { h : E → F | ∃ (c : S k)
          (f : S k → F), Quad f ∧ ∀ s : E, h s = f s + triple a b c s } from
        ⟨0, 0, quad_zero, by simp [triple]⟩)
    · simpa only [one_smul] using hu

lemma dual_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι] (l : (ι → F) →ₗ[F] F)
    (x : ι → F) : l x = ∑ j, (l (Pi.single j 1)) * x j := by
  calc
    l x = l (∑ j, Pi.single j (x j)) :=
      congrArg l (LinearMap.sum_single_apply (φ := fun _ : ι => F) x).symm
    _ = _ := ?_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rcases field_cases (x j) with hj | hj <;> simp [hj]

lemma dual_finset {k : ℕ} (E : Finset (S k)) (l : (E → F) →ₗ[F] F) :
    ∃ U ⊆ E, ∀ f : S k → F, l (fun x : E => f x) = ∑ s ∈ U, f s := by
  classical
  let t : Finset E := Finset.univ.filter (fun s => l (Pi.single s 1) = 1)
  let U := t.image Subtype.val
  refine ⟨U, ?_, fun f => ?_⟩
  · intro s hs
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hs
    exact x.property
  · rw [dual_coordinates, Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    simp only [t, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases field_cases (l (Pi.single j 1)) with h | h <;> simp [h]

lemma good_iff {k : ℕ} (E : Finset (S k)) (a b : S k) :
    Good E a b ↔ ∀ U ∈ Rel E, U.Nonempty → ∃ c : S k, (∑ s ∈ U, triple a b c s) = 1 := by
  classical
  constructor
  · intro hg U hU hne
    obtain ⟨u, hu⟩ := hne
    let h : S k → F := fun s => if s = u then 1 else 0
    obtain ⟨c, f, hf, hfit⟩ := hg h
    refine ⟨c, ?_⟩
    obtain ⟨hs, hsum⟩ := mem_rel.mp hU
    have eq : ∑ s ∈ U, h s = ∑ s ∈ U, (f s + triple a b c s) :=
      Finset.sum_congr rfl fun s hs' => hfit s (hs hs')
    rw [Finset.sum_add_distrib, hsum f hf, zero_add] at eq
    rw [← eq]
    simp [h, hu]
  · intro ha h
    by_contra hn
    let W := fits E a b
    have hx : (fun s : E => h s) ∉ W := by
      rintro ⟨c, f, hf, he⟩
      exact hn ⟨c, f, hf, fun s hs => he ⟨s, hs⟩⟩
    obtain ⟨l, hl, hk⟩ := W.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hv (x : E → F) (hx' : x ∈ W) : l x = 0 := by
      have hm : l x ∈ W.map l := Submodule.mem_map_of_mem hx'
      rwa [hk, Submodule.mem_bot] at hm
    obtain ⟨U, hs, hU⟩ := dual_finset E l
    have hU' : U ∈ Rel E := mem_rel.mpr ⟨hs, fun f hf => by
      rw [← hU f]
      apply hv
      exact ⟨0, f, hf, by simp [triple]⟩⟩
    have hne : U.Nonempty := by
      contrapose! hl
      rw [hU h, hl, Finset.sum_empty]
    obtain ⟨c, hc⟩ := ha U hU' hne
    have hz := hv (fun s : E => triple a b c s) ⟨c, 0, quad_zero, by simp⟩
    rw [hU (triple a b c), hc] at hz
    exact one_ne_zero hz

end QL990

namespace QL990

lemma quad_const {k : ℕ} (b : F) : Quad (fun _ : S k => b) := ⟨b, 0, 0, by simp⟩

lemma quad_dot {k : ℕ} (a : S k) : Quad (dotProduct a) := ⟨0, a, 0, by simp⟩

lemma quad_scale {k : ℕ} {f : S k → F} (a : F) (hf : Quad f) :
    Quad (fun x => a * f x) := by
  rcases field_cases a with rfl | rfl
  · simpa using (quad_const (k := k) 0)
  · simpa using hf

lemma quad_sum {ι : Type*} {k : ℕ} (t : Finset ι) (f : ι → S k → F)
    (h : ∀ i ∈ t, Quad (f i)) : Quad (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (quad_const (k := k) 0)
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact
      quad_add (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma quad_dot_mul {k : ℕ} (a b : S k) : Quad (fun x => dotProduct a x * dotProduct b x) := by
  refine ⟨0, 0, fun i j => a i * b j, fun x => ?_⟩
  rw [zero_dotProduct, add_zero, zero_add]
  simp only [dotProduct, Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quad_affine_mul {k : ℕ} (a b : S k) (p q : F) :
    Quad (fun x => (p + dotProduct a x) * (q + dotProduct b x)) := by
  convert quad_add (quad_add (quad_const (k := k) (p*q)) (quad_scale p (quad_dot b)))
    (quad_add (quad_scale q (quad_dot a)) (quad_dot_mul a b)) using 1
  ext x
  simp only [Pi.add_apply]
  ring

lemma triple_affine_part {k : ℕ} (a b c : S k) (p q r : F) : ∃ f, Quad f ∧ ∀ x,
    (p + dotProduct a x) * (q + dotProduct b x) * (r + dotProduct c x) = f x + triple a b c x := by
  refine ⟨_, quad_add (quad_scale r (quad_affine_mul a b p q))
    (quad_add (quad_scale (p*q) (quad_dot c))
      (quad_add (quad_scale p (quad_dot_mul b c)) (quad_scale q (quad_dot_mul a c)))), fun x => ?_⟩
  simp only [Pi.add_apply, triple]
  ring

noncomputable def linDot {k : ℕ} (a : S k) : S k →ₗ[F] F where
  toFun := dotProduct a
  map_add' := dotProduct_add a
  map_smul' := by intro c x; exact dotProduct_smul c a x

noncomputable def pull {m n : ℕ} (B : S m →ₗ[F] S n) (a : S n) : S m :=
  fun i => dotProduct a (B (Pi.single i 1))

lemma dot_pull {m n : ℕ} (B : S m →ₗ[F] S n) (a : S n) (x : S m) :
    dotProduct a (B x) = dotProduct (pull B a) x :=
  dual_coordinates ((linDot a).comp B) x

lemma dot_pull_affine {m n : ℕ} (B : S m →ₗ[F] S n) (o a : S n) (x : S m) :
    dotProduct a (o + B x) = dotProduct a o + dotProduct (pull B a) x := by
  rw [dotProduct_add, dot_pull]

lemma quad_pull {m n : ℕ} (B : S m →ₗ[F] S n) (o : S n) {f : S n → F} (hf : Quad f) :
    Quad (fun x => f (o + B x)) := by
  classical
  obtain ⟨c, a, M, hf⟩ := hf
  have hlin : Quad (fun x => dotProduct a (o + B x)) := by
    simp_rw [dot_pull_affine]
    exact
      quad_add (quad_const (k := m) (dotProduct a o)) (quad_dot (pull B a))
  have hcoord (i : Fin n) (x : S m) :
      (o + B x) i = o i + dotProduct (pull B (Pi.single i 1)) x := by
    simpa only [single_one_dotProduct] using dot_pull_affine B o (Pi.single i 1) x
  have hprod (i j : Fin n) : Quad (fun x : S m =>
      M i j * (o + B x) i * (o + B x) j) := by
    simpa only [hcoord, mul_assoc] using quad_scale (M i j)
      (quad_affine_mul (pull B (Pi.single i 1)) (pull B (Pi.single j 1)) (o i) (o j))
  simp only [hf]
  exact quad_add (quad_add (quad_const (k := m) c) hlin)
    (quad_sum Finset.univ (fun i x => ∑ j, M i j * (o + B x) i * (o + B x) j)
      (fun i _ => quad_sum Finset.univ _ (fun j _ => hprod i j)))

noncomputable def place {m n : ℕ} (B : S m →ₗ[F] S n) (o : S n) := fun x => o + B x

lemma place_injective {m n : ℕ} {B : S m →ₗ[F] S n} (o : S n) (hB : Function.Injective B) :
    Function.Injective (place B o) := fun _ _ h => hB (add_left_cancel h)

lemma undo_place {m n : ℕ} {B : S m →ₗ[F] S n} {D : S n →ₗ[F] S m}
    (hD : D.comp B = LinearMap.id) (o : S n) (x : S m) : place D (-(D o)) (place B o x) = x := by
  have he := DFunLike.congr_fun hD x
  change D (B x) = x at he
  simp [place, he]

lemma pull_surj {m n : ℕ} {B : S m →ₗ[F] S n} {D : S n →ₗ[F] S m}
    (hD : D.comp B = LinearMap.id) : Function.Surjective (pull B) := by
  intro a
  refine ⟨pull D a, ?_⟩
  funext i
  have hi := DFunLike.congr_fun hD (Pi.single i 1)
  change D (B (Pi.single i 1)) = Pi.single i 1 at hi
  change dotProduct (pull D a) (B (Pi.single i 1)) = a i
  rw [← dot_pull, hi]
  simp

lemma fit_affine_iff {m n : ℕ} (B : S m →ₗ[F] S n) (D : S n →ₗ[F] S m)
    (hD : D.comp B = LinearMap.id) (o : S n) (E : Finset (S m)) (a b : S n) (h : S n → F) :
    Fit (E.image (place B o)) a b h ↔
      Fit E (pull B a) (pull B b) (fun x => h (place B o x)) := by
  classical
  have corr (c : S n) : ∃ q : S m → F, Quad q ∧ ∀ x,
      triple a b c (place B o x) = q x + triple (pull B a) (pull B b) (pull B c) x := by
    simpa only [triple, place, dot_pull_affine] using
      triple_affine_part (pull B a) (pull B b) (pull B c) (dotProduct a o) (dotProduct b o) (dotProduct c o)
  constructor
  · rintro ⟨c, f, hf, hfc⟩
    obtain ⟨q, hq, he⟩ := corr c
    refine ⟨pull B c, (fun x => f (place B o x)) + q, quad_add (quad_pull B o hf) hq, ?_⟩
    intro x hx
    change h (place B o x) = (fun t => f (place B o t)) x + q x + _
    exact (hfc _ (Finset.mem_image_of_mem _ hx)).trans (by rw [he, add_assoc])
  · rintro ⟨c, f, hf, hfc⟩
    obtain ⟨c', hc⟩ := pull_surj hD c
    obtain ⟨q, hq, he⟩ := corr c'
    refine ⟨c', (fun y => (f+q) (place D (-(D o)) y)), quad_pull D (-(D o)) (quad_add hf hq), ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    change h (place B o x) = (f + q) (place D (-(D o)) (place B o x)) + _
    have hx' : h (place B o x) = _ := hfc x hx
    rw [undo_place hD, he, hc, hx', Pi.add_apply]
    rw [add_assoc, ← add_assoc (q x), ZModModule.add_self, zero_add]

lemma good_affine_iff {m n : ℕ} (B : S m →ₗ[F] S n) (D : S n →ₗ[F] S m)
    (hD : D.comp B = LinearMap.id) (o : S n) (E : Finset (S m)) (a b : S n) :
    Good (E.image (place B o)) a b ↔ Good E (pull B a) (pull B b) := by
  constructor
  · intro hg h
    have hh := (fit_affine_iff B D hD o E a b _).mp (hg (fun y => h (place D (-(D o)) y)))
    simpa only [undo_place hD] using hh
  · intro hg h
    exact (fit_affine_iff B D hD o E a b h).mpr (hg _)

lemma rel_affine_card {m n : ℕ} (B : S m →ₗ[F] S n) (D : S n →ₗ[F] S m)
    (hD : D.comp B = LinearMap.id) (hB : Function.Injective B) (o : S n) (E : Finset (S m)) :
    (Rel (E.image (place B o))).card = (Rel E).card := by
  classical
  let J : S m ↪ S n := ⟨place B o, place_injective o hB⟩
  have hsum (U : Finset (S m)) (f : S n → F) :
      (∑ y ∈ U.image J, f y) = ∑ x ∈ U, f (J x) :=
    Finset.sum_image (fun _ _ _ _ h => J.injective h)
  have hm (U : Finset (S m)) : U.image J ∈ Rel (E.image J) ↔ U ∈ Rel E := by
    simp only [mem_rel, hsum]
    constructor
    · rintro ⟨hs, hp⟩
      refine ⟨?_, fun f hf => ?_⟩
      · intro x hx
        obtain ⟨y, hy, he⟩ := Finset.mem_image.mp (hs (Finset.mem_image_of_mem J hx))
        exact J.injective he ▸ hy
      · have hi := hp (fun y => f (place D (-(D o)) y)) (quad_pull D (-(D o)) hf)
        simpa only [show ∀ x, place D (-(D o)) (J x) = x from undo_place hD o] using hi
    · rintro ⟨hs, hp⟩
      exact ⟨Finset.image_subset_image hs, fun f hf => hp _ (quad_pull B o hf)⟩
  change (Rel (E.image J)).card = (Rel E).card
  rw [← Finset.card_image_of_injective (Rel E) (Finset.image_injective J.injective)]
  congr 1
  ext U
  constructor
  · intro hu
    let V := E.filter (fun x => J x ∈ U)
    have he : V.image J = U := by
      ext y
      constructor
      · rintro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hx).2
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ((mem_rel.mp hu).1 hy)
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, hy⟩)
    exact Finset.mem_image.mpr ⟨V, (hm V).mp (he.symm ▸ hu), he⟩
  · intro hu
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hu
    exact (hm V).mpr hV

lemma affine_result {m n : ℕ} (B : S m →ₗ[F] S n) (o : S n) (E : Finset (S m))
    (hB : Function.Injective B)
    (hb : (Rel E).card = 8 ∧ (∀ h, ∃ a b, Fit E a b h) ∧ ¬∃ a b, Good E a b) :
    let V := E.image (fun x => o + B x)
    (Rel V).card = 8 ∧ (∀ h, ∃ a b, Fit V a b h) ∧ ¬∃ a b, Good V a b := by
  obtain ⟨D, hD⟩ := B.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hB)
  refine ⟨(rel_affine_card B D hD hB o E).trans hb.1, ?_, ?_⟩
  · intro h
    obtain ⟨a, b, hab⟩ := hb.2.1 (fun x => h (place B o x))
    obtain ⟨a', ha⟩ := pull_surj hD a
    obtain ⟨b', hb'⟩ := pull_surj hD b
    refine ⟨a', b', (fit_affine_iff B D hD o E a' b' h).mpr ?_⟩
    simpa only [ha, hb'] using hab
  · rintro ⟨a, b, hab⟩
    exact hb.2.2 ⟨pull B a, pull B b, (good_affine_iff B D hD o E a b).mp hab⟩

end QL990

namespace QL990

private lemma alt_mem_rel {k : ℕ} {E U : Finset (S k)} :
    U ∈ Rel E ↔ U ⊆ E ∧ ∀ f : S k → F, Quad f → (∑ s ∈ U, f s) = 0 := by
  classical
  simp [Rel]

private lemma alt_bit_cases (x : F) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

private lemma alt_mul_self (x : F) : x * x = x := by
  rcases alt_bit_cases x with rfl | rfl <;> simp

private lemma alt_quad_const {k : ℕ} (d : F) : Quad (fun _ : S k => d) :=
  ⟨d, 0, 0, by simp⟩

private lemma alt_quad_dot {k : ℕ} (a : S k) : Quad (fun s => dotProduct a s) :=
  ⟨0, a, 0, by simp⟩

private lemma alt_quad_pair {k : ℕ} (a b : S k) :
    Quad (fun s => dotProduct a s * dotProduct b s) := by
  refine ⟨0, 0, fun i j => a i * b j, fun s => ?_⟩
  simp only [zero_dotProduct, add_zero, zero_add]
  calc
    dotProduct a s * dotProduct b s =
        ∑ i, ∑ j, (a i * s i) * (b j * s j) := by
      unfold dotProduct
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ j, (a i * b j) * s i * s j := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

private def alt_dot_linear {k : ℕ} (s : S k) : S k →ₗ[F] F where
  toFun a := dotProduct a s
  map_add' a b := add_dotProduct a b s
  map_smul' r a := by
    rw [RingHom.id_apply, smul_dotProduct]

private lemma alt_dot_linear_apply {k : ℕ} (s a : S k) :
    alt_dot_linear s a = dotProduct a s := rfl

noncomputable def T {k : ℕ} (U : Finset (S k)) : S k →ₗ[F] S k →ₗ[F] S k →ₗ[F] F :=
  ∑ s ∈ U, (alt_dot_linear s).smulRight ((alt_dot_linear s).smulRight (alt_dot_linear s))

@[simp] theorem T_apply {k : ℕ} (U : Finset (S k)) (a b c : S k) :
    T U a b c = ∑ s ∈ U, triple a b c s := by
  simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
    alt_dot_linear_apply, smul_eq_mul, triple, mul_assoc]

theorem T_swap₁₂ {k : ℕ} (U : Finset (S k)) (a b c : S k) : T U a b c = T U b a c := by
  simp only [T_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [triple, mul_comm (dotProduct a s) (dotProduct b s)]

theorem T_swap₂₃ {k : ℕ} (U : Finset (S k)) (a b c : S k) : T U a b c = T U a c b := by
  simp only [T_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [triple, mul_assoc, mul_comm (dotProduct b s) (dotProduct c s)]

theorem T_eq_zero₁₂ {k : ℕ} {E U : Finset (S k)} (hU : U ∈ Rel E) (a c : S k) :
    T U a a c = 0 := by
  rw [T_apply]
  calc
    (∑ s ∈ U, triple a a c s) = ∑ s ∈ U, dotProduct a s * dotProduct c s := by
      simp only [triple, alt_mul_self]
    _ = 0 := (alt_mem_rel.mp hU).2 _ (alt_quad_pair a c)

theorem T_eq_zero₁₃ {k : ℕ} {E U : Finset (S k)} (hU : U ∈ Rel E) (a b : S k) :
    T U a b a = 0 :=
  (T_swap₂₃ U a b a).trans (T_eq_zero₁₂ hU a b)

theorem T_eq_zero₂₃ {k : ℕ} {E U : Finset (S k)} (hU : U ∈ Rel E) (a b : S k) :
    T U a b b = 0 :=
  (T_swap₁₂ U a b b).trans (T_eq_zero₁₃ hU b a)

private lemma alt_weighted_sum {k : ℕ} {E U : Finset (S k)}
    (hU : U ∈ Rel E) (hT : T U = 0) (a : S k) {f : S k → F} (hf : Quad f) :
    (∑ s ∈ U, dotProduct a s * f s) = 0 := by
  obtain ⟨d, l, M, hrep⟩ := hf
  have hlin : (∑ s ∈ U, dotProduct a s) = 0 := (alt_mem_rel.mp hU).2 _ (alt_quad_dot a)
  have hpair : (∑ s ∈ U, dotProduct a s * dotProduct l s) = 0 :=
    (alt_mem_rel.mp hU).2 _ (alt_quad_pair a l)
  have hcoeff (i j : Fin k) : (∑ s ∈ U, dotProduct a s * (M i j * s i * s j)) = 0 := by
    calc
      _ = M i j * T U a (Pi.single i 1) (Pi.single j 1) := by
        rw [T_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [triple, single_dotProduct, one_mul]
        ring
      _ = 0 := by rw [hT] <;> simp
  have hmat : (∑ s ∈ U, dotProduct a s * (∑ i, ∑ j, M i j * s i * s j)) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun j _ => hcoeff i j
  simp only [hrep, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hlin, hpair, hmat] <;> simp

private lemma alt_affine_one_cut {k : ℕ} {E U : Finset (S k)}
    (hU : U ∈ Rel E) (hT : T U = 0) (d : F) (a : S k) :
    U.filter (fun s => d + dotProduct a s = 1) ∈ Rel E := by
  refine alt_mem_rel.mpr ⟨(Finset.filter_subset (fun s => d + dotProduct a s = 1) U).trans
    (alt_mem_rel.mp hU).1, ?_⟩
  intro f hf
  rw [Finset.sum_filter]
  calc
    (∑ s ∈ U, if d + dotProduct a s = 1 then f s else 0) =
        ∑ s ∈ U, (d + dotProduct a s) * f s := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rcases alt_bit_cases (d + dotProduct a s) with h | h <;> simp [h]
    _ = 0 := by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, (alt_mem_rel.mp hU).2 f hf, alt_weighted_sum hU hT a hf] <;> simp

theorem T_affine_cut_mem_Rel {k : ℕ} {E U : Finset (S k)}
    (hU : U ∈ Rel E) (hT : T U = 0) (d : F) (a : S k) (r : F) :
    U.filter (fun s => d + dotProduct a s = r) ∈ Rel E := by
  have hcut : U.filter (fun s => d + dotProduct a s = r) =
      U.filter (fun s => ((1 - r) + d) + dotProduct a s = 1) := by
    apply Finset.ext
    intro s
    simp only [Finset.mem_filter, add_assoc]
    have hr : (1 - r) + r = 1 := sub_add_cancel 1 r
    constructor
    · rintro ⟨hs, hval⟩
      exact ⟨hs, by rw [hval, hr]⟩
    · rintro ⟨hs, hval⟩
      exact ⟨hs, add_left_cancel (hval.trans hr.symm)⟩
  rw [hcut]
  exact alt_affine_one_cut hU hT ((1 - r) + d) a

theorem T_linear_cut_mem_Rel {k : ℕ} {E U : Finset (S k)}
    (hU : U ∈ Rel E) (hT : T U = 0) (a : S k) (r : F) :
    U.filter (fun s => dotProduct a s = r) ∈ Rel E := by
  simpa only [zero_add] using T_affine_cut_mem_Rel hU hT 0 a r

theorem T_coord_cut_mem_Rel {k : ℕ} {E U : Finset (S k)}
    (hU : U ∈ Rel E) (hT : T U = 0) (i : Fin k) (r : F) :
    U.filter (fun s => s i = r) ∈ Rel E := by
  simpa only [single_dotProduct, one_mul] using T_linear_cut_mem_Rel hU hT (Pi.single i 1) r

private lemma alt_exists_distinct_coord {k : ℕ} {x y : S k} (hxy : x ≠ y) :
    ∃ i, x i ≠ y i := by
  classical
  by_contra! h
  exact hxy (funext h)

theorem T_separates_points {k : ℕ} {E U : Finset (S k)}
    (hU : U ∈ Rel E) (hT : T U = 0) {x y : S k} (hx : x ∈ U) (hxy : x ≠ y) :
    ∃ V ∈ Rel E, V ⊆ U ∧ x ∈ V ∧ y ∉ V := by
  obtain ⟨i, hi⟩ := alt_exists_distinct_coord hxy
  exact ⟨U.filter (fun s => s i = x i), T_coord_cut_mem_Rel hU hT i (x i),
    Finset.filter_subset _ U, Finset.mem_filter.mpr ⟨hx, rfl⟩,
    fun hy => hi (Finset.mem_filter.mp hy).2.symm⟩

theorem alt_rel_card_ge_four {k : ℕ} {E U : Finset (S k)}
    (hU : U ∈ Rel E) (hUn : U.Nonempty) : 4 ≤ U.card := by
  classical
  have heven : 2 ∣ U.card := (ZMod.natCast_eq_zero_iff U.card 2).mp (by
    simpa only [Finset.sum_const, nsmul_one] using
      (alt_mem_rel.mp hU).2 (fun _ => 1) (alt_quad_const 1))
  obtain ⟨m, hm⟩ := heven
  have hpos := hUn.card_pos
  by_contra! hsmall
  have htwo : U.card = 2 := by omega
  obtain ⟨x, y, hxy, hUxy⟩ := Finset.card_eq_two.mp htwo
  obtain ⟨i, hi⟩ := alt_exists_distinct_coord hxy
  have hz := (alt_mem_rel.mp hU).2 (fun s => dotProduct (Pi.single i 1) s)
    (alt_quad_dot (Pi.single i 1))
  rw [hUxy] at hz
  have hpair : x i + y i = 0 := by simpa [hxy] using hz
  have hsub := congrArg (fun z : F => z - y i) hpair
  exact hi (by simpa only [add_sub_cancel_right, zero_sub, ZMod.neg_eq_self_mod_two] using hsub)

theorem T_ne_zero {k : ℕ} {E U : Finset (S k)}
    (hU : U ∈ Rel E) (hUn : U.Nonempty) (hcard : (Rel E).card ≤ 4) : T U ≠ 0 := by
  classical
  intro hT
  have hlarge := alt_rel_card_ge_four hU hUn
  have hUneq := hUn.ne_empty
  obtain ⟨x, hx⟩ := hUn
  have hpair : ∃ y ∈ U, x ≠ y := by
    by_contra! h
    have hsub : U ⊆ ({x} : Finset (S k)) := by
      intro y hy
      exact Finset.mem_singleton.mpr (h y hy).symm
    have hsmall := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hsmall
    omega
  obtain ⟨y, hy, hxy⟩ := hpair
  obtain ⟨V, hV, hVU, hxV, hyV⟩ := T_separates_points hU hT hx hxy
  let W := U \ V
  have hW : W ∈ Rel E := by
    refine alt_mem_rel.mpr ⟨(Finset.sdiff_subset : W ⊆ U).trans (alt_mem_rel.mp hU).1, ?_⟩
    intro f hf
    have h := Finset.sum_sdiff (f := f) hVU
    rw [(alt_mem_rel.mp hV).2 f hf, add_zero, (alt_mem_rel.mp hU).2 f hf] at h
    exact h
  have hE0 : ∅ ∈ Rel E := alt_mem_rel.mpr ⟨Finset.empty_subset _, by simp⟩
  have hyW : y ∈ W := Finset.mem_sdiff.mpr ⟨hy, hyV⟩
  have hxW : x ∉ W := fun h => (Finset.mem_sdiff.mp h).2 hxV
  have hVneU : V ≠ U := fun h => hyV (by rw [h]; exact hy)
  have hWneU : W ≠ U := fun h => hxW (by rw [h]; exact hx)
  have hWneV : W ≠ V := fun h => hxW (by rw [h]; exact hxV)
  let K : Finset (Finset (S k)) := {W, V, U, ∅}
  have hKsub : K ⊆ Rel E := by
    intro R hR
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · exact hW
    · exact hV
    · exact hU
    · exact hE0
  have hKcard : K.card = 4 := by
    have h₁ : U ∉ ({∅} : Finset (Finset (S k))) := by simpa only [Finset.mem_singleton] using hUneq
    have h₂ : V ∉ ({U, ∅} : Finset (Finset (S k))) := by
      simp [hVneU, Finset.ne_empty_of_mem hxV]
    have h₃ : W ∉ ({V, U, ∅} : Finset (Finset (S k))) := by
      simp [hWneV, hWneU, Finset.ne_empty_of_mem hyW]
    simp only [K, Finset.card_insert_of_notMem h₃, Finset.card_insert_of_notMem h₂,
      Finset.card_insert_of_notMem h₁, Finset.card_singleton]
  have hexhaust : K = Rel E := Finset.eq_of_subset_of_card_le hKsub (by rwa [hKcard])

  have hunique {p q : S k} (hp : p ∈ U) (hq : q ∈ U) (hpq : p ∈ V ↔ q ∈ V) : p = q := by
    by_contra hne
    obtain ⟨R, hR, _, hpR, hqR⟩ := T_separates_points hU hT hp hne
    rw [← hexhaust] at hR
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · exact hqR (Finset.mem_sdiff.mpr ⟨hq, fun hqV => (Finset.mem_sdiff.mp hpR).2 (hpq.mpr hqV)⟩)
    · exact hqR (hpq.mp hpR)
    · exact hqR hq
    · simpa using hpR
  have hVcard : V.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    exact hunique (hVU hp) (hVU hq) ⟨fun _ => hq, fun _ => hp⟩
  have hWcard : W.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hpU, hpV⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hqU, hqV⟩ := Finset.mem_sdiff.mp hq
    exact hunique hpU hqU ⟨fun h => (hpV h).elim, fun h => (hqV h).elim⟩
  have hsplit : W.card = U.card - V.card := Finset.card_sdiff_of_subset hVU
  omega

end QL990

namespace QL990.Counting

abbrev Bilinear (k : ℕ) := S k →ₗ[F] S k →ₗ[F] F
abbrev Trilinear (k : ℕ) := S k →ₗ[F] Bilinear k

def IsAlternating {k : ℕ} (A : Trilinear k) : Prop :=
  (∀ x z, A x x z = 0) ∧ (∀ x y, A x y x = 0) ∧ (∀ x y, A x y y = 0)

private theorem eq_one_of_nonzero {x : F} (hx : x ≠ 0) : x = 1 := by
  fin_cases x <;> first | exact False.elim (hx rfl) | rfl

private theorem active_iff {k : ℕ} (f : S k →ₗ[F] F) :
    (∃ c, f c = 1) ↔ f ≠ 0 := by
  constructor
  · rintro ⟨c, hc⟩ rfl
    simpa using hc
  · intro hf
    by_contra! h
    apply hf
    apply LinearMap.ext
    intro c
    have hz : f c = 0 := by
      by_contra hc
      exact h c (eq_one_of_nonzero hc)
    simpa only [LinearMap.zero_apply] using hz

private theorem shifts_bound {k d : ℕ} (U : Finset (S k))
    (L : S k →ₗ[F] S d) (hs : Function.Surjective L) (hU : ∀ a ∈ U, L a = 0) :
    2 ^ d * U.card ≤ Fintype.card (S k) := by
  classical
  choose lift hl using hs
  let g : S d × U → S k := fun p => lift p.1 + p.2.val
  have hg : Function.Injective g := by
    intro p q hpq
    have e1 : p.1 = q.1 := by
      have hh := congrArg (fun x => L x) hpq
      change L (lift p.1 + p.2.val) = L (lift q.1 + q.2.val) at hh
      simpa only [map_add, hl, hU _ p.2.property, hU _ q.2.property, add_zero] using hh
    have e2 : p.2 = q.2 := by
      apply Subtype.ext
      change lift p.1 + p.2.val = lift q.1 + q.2.val at hpq
      rw [e1] at hpq
      exact add_left_cancel hpq
    exact Prod.ext e1 e2
  have hc := Fintype.card_le_of_injective g hg
  rw [Fintype.card_prod, Fintype.card_coe] at hc
  have hd : Fintype.card (S d) = 2 ^ d := by simp [F, ZMod.card]
  rwa [hd] at hc

private def evalPair {k : ℕ} (y z : S k) : Bilinear k →ₗ[F] F :=
  (LinearMap.applyₗ z).comp (LinearMap.applyₗ y)

private theorem trilinear_bound {k : ℕ} (A : Trilinear k) (hA : A ≠ 0)
    (halt : IsAlternating A) (U : Finset (S k)) (hU : ∀ a ∈ U, A a = 0) :
    8 * U.card ≤ Fintype.card (S k) := by
  obtain ⟨h₁₂, h₁₃, _⟩ := halt
  obtain ⟨p, q, r, hpqr⟩ : ∃ p q r, A p q r ≠ 0 := by
    by_contra! h
    apply hA
    exact LinearMap.ext fun p => LinearMap.ext fun q => LinearMap.ext fun r => by
      simpa only [LinearMap.zero_apply] using h p q r
  have hp : A p q r = 1 := eq_one_of_nonzero hpqr
  have hq : A q p r = 1 := by
    have h : A q p r + A p q r = 0 := by
      simpa only [map_add, LinearMap.add_apply, h₁₂, zero_add, add_zero] using h₁₂ (p + q) r
    exact (CharTwo.add_eq_zero.mp h).trans hp
  have hr : A r q p = 1 := by
    have h : A r q p + A p q r = 0 := by
      simpa only [map_add, LinearMap.add_apply, h₁₃, zero_add, add_zero] using h₁₃ (p + r) q
    exact (CharTwo.add_eq_zero.mp h).trans hp
  let ev : Bilinear k →ₗ[F] (Fin 3 → F) :=
    LinearMap.pi (φ := fun _ : Fin 3 => F) ![evalPair q r, evalPair p r, evalPair q p]
  have he : Function.Surjective (ev.comp A) := by
    intro v
    let x : S k := v 0 • p + v 1 • q + v 2 • r
    refine ⟨x, funext fun i => ?_⟩
    simp only [LinearMap.comp_apply, ev, LinearMap.pi_apply]
    fin_cases i <;>
      simp [evalPair, x, h₁₂, h₁₃, hp, hq, hr]
  have hh := shifts_bound U (ev.comp A) he (fun a ha => by
    rw [LinearMap.comp_apply, hU a ha, map_zero])
  rwa [show 2 ^ 3 = (8 : ℕ) from rfl] at hh

private theorem bilinear_bound {k : ℕ} (B : Bilinear k) (hB : B ≠ 0)
    (halt : ∀ y, B y y = 0) (U : Finset (S k)) (hU : ∀ a ∈ U, B a = 0) :
    4 * U.card ≤ Fintype.card (S k) := by
  obtain ⟨p, q, hpq⟩ : ∃ p q, B p q ≠ 0 := by
    by_contra! h
    apply hB
    exact LinearMap.ext fun p => LinearMap.ext fun q => by
      simpa only [LinearMap.zero_apply] using h p q
  have hp : B p q = 1 := eq_one_of_nonzero hpq
  have hq : B q p = 1 := by
    have h : B q p + B p q = 0 := by
      simpa only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] using halt (p + q)
    exact (CharTwo.add_eq_zero.mp h).trans hp
  let ev : (S k →ₗ[F] F) →ₗ[F] (Fin 2 → F) :=
    LinearMap.pi (φ := fun _ : Fin 2 => F) ![LinearMap.applyₗ q, LinearMap.applyₗ p]
  have he : Function.Surjective (ev.comp B) := by
    intro v
    let x : S k := v 0 • p + v 1 • q
    refine ⟨x, funext fun i => ?_⟩
    simp only [LinearMap.comp_apply, ev, LinearMap.pi_apply]
    fin_cases i <;> simp [x, halt, hp, hq]
  have hh := shifts_bound U (ev.comp B) he (fun a ha => by
    rw [LinearMap.comp_apply, hU a ha, map_zero])
  rwa [show 2 ^ 2 = (4 : ℕ) from rfl] at hh

private theorem union_bound {α ι : Type*} [Fintype α] [DecidableEq α]
    (I : Finset ι) (T : ι → Finset α) (hI : I.card ≤ 3) (d : ℕ)
    (hT : ∀ i ∈ I, d * (T i).card ≤ Fintype.card α) :
    d * Fintype.card α ≤ d * (Finset.univ \ I.biUnion T).card + 3 * Fintype.card α := by
  let N := Fintype.card α
  let B := I.biUnion T
  have hc : (Finset.univ \ B).card + B.card = N := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B), Finset.card_univ]
  have hbad : d * B.card ≤ 3 * N := calc
    _ ≤ d * ∑ i ∈ I, (T i).card := Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ i ∈ I, d * (T i).card := Finset.mul_sum _ _ _
    _ ≤ ∑ _i ∈ I, N := Finset.sum_le_sum hT
    _ = I.card * N := Finset.sum_const_nat (fun _ _ => rfl)
    _ ≤ 3 * N := Nat.mul_le_mul_right N hI
  change d * N ≤ d * (Finset.univ \ B).card + 3 * N
  conv_lhs => rw [← hc, Nat.mul_add]
  exact Nat.add_le_add_left hbad _

theorem count_active {k : ℕ} {ι : Type*} (I : Finset ι) (A : ι → Trilinear k)
    (hI : I.card ≤ 3) (hA : ∀ i ∈ I, A i ≠ 0 ∧ IsAlternating (A i))
    (P : S k → S k → Prop) (hP : ∀ a b, P a b ↔ ∀ i ∈ I, A i a b ≠ 0) :
    5 * 2 ^ (2 * k) ≤ 32 * ((Finset.univ : Finset (S k × S k)).filter
      (fun v => @decide (P v.1 v.2) (Classical.propDecidable _))).card := by
  classical
  let good : Finset (S k × S k) := Finset.univ.filter
    (fun v => @decide (P v.1 v.2) (Classical.propDecidable _))
  let N := Fintype.card (S k)
  let K (i : ι) : Finset (S k) := Finset.univ.filter (fun a => A i a = 0)
  let goodFirst := (Finset.univ : Finset (S k)) \ I.biUnion K
  have hFirst : 5 * N ≤ 8 * goodFirst.card := by
    have hK (i : ι) (hi : i ∈ I) : 8 * (K i).card ≤ N := by
      exact trilinear_bound (A i) (hA i hi).1 (hA i hi).2 (K i)
        (fun _ ha => (Finset.mem_filter.mp ha).2)
    have h := union_bound I K hI 8 hK
    change 8 * N ≤ 8 * goodFirst.card + 3 * N at h
    omega
  let row : S k → Finset (S k) := fun a => Finset.univ.filter
    (fun b => @decide (P a b) (Classical.propDecidable _))
  have hRow (a : S k) (ha : a ∈ goodFirst) : N ≤ 4 * (row a).card := by
    let J (i : ι) : Finset (S k) := Finset.univ.filter (fun b => A i a b = 0)
    have hn (i) (hi : i ∈ I) : A i a ≠ 0 := by
      intro hz
      exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩)
    have he : row a = Finset.univ \ I.biUnion J := by
      ext b
      simp only [row, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, hP,
        Finset.mem_sdiff, Finset.mem_biUnion, J]
      exact ⟨fun h ⟨i, hi, hz⟩ => h i hi hz, fun h i hi hz => h ⟨i, hi, hz⟩⟩
    have hJ (i : ι) (hi : i ∈ I) : 4 * (J i).card ≤ N :=
      bilinear_bound (A i a) (hn i hi) ((hA i hi).2.2.2 a) (J i)
        (fun _ hb => (Finset.mem_filter.mp hb).2)
    have h := union_bound I J hI 4 hJ
    rw [← he] at h
    change 4 * N ≤ 4 * (row a).card + 3 * N at h
    omega
  have hRows : good.card = ∑ a : S k, (row a).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (s := good) (by intro v hv; exact Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.card_bij (fun v _ => v.2) ?_ ?_ ?_
    · rintro ⟨x, y⟩ hv
      obtain ⟨hxy, hxa⟩ := Finset.mem_filter.mp hv
      change x = a at hxa
      subst x
      simpa [row, good] using hxy
    · intro v hv w hw hvw
      exact Prod.ext ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm) hvw
    · intro b hb
      exact ⟨(a,b), Finset.mem_filter.mpr ⟨by simpa [good, row] using hb, rfl⟩, rfl⟩
  have hSum : goodFirst.card * N ≤ 4 * good.card := calc
    _ = ∑ _a ∈ goodFirst, N := (Finset.sum_const_nat (fun _ _ => rfl)).symm
    _ ≤ ∑ a ∈ goodFirst, 4 * (row a).card := Finset.sum_le_sum hRow
    _ ≤ ∑ a : S k, 4 * (row a).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := by rw [hRows, Finset.mul_sum]
  have hN : N = 2 ^ k := by simp [N, F, ZMod.card]
  have hsquare : N ^ 2 = 2 ^ (2 * k) := by rw [hN, Nat.mul_comm 2 k, pow_mul]
  change 5 * 2 ^ (2 * k) ≤ 32 * good.card
  calc
    _ = (5 * N) * N := by rw [← hsquare, pow_two, Nat.mul_assoc]
    _ ≤ (8 * goodFirst.card) * N := Nat.mul_le_mul_right _ hFirst
    _ = 8 * (goodFirst.card * N) := Nat.mul_assoc _ _ _
    _ ≤ 8 * (4 * good.card) := Nat.mul_le_mul_left _ hSum
    _ = _ := by rw [← Nat.mul_assoc]

theorem count_good {k : ℕ} (E : Finset (S k)) (A : Finset (S k) → Trilinear k)
    (hcard : (Rel E).card ≤ 4)
    (hA : ∀ U ∈ Rel E, U.Nonempty → A U ≠ 0 ∧ IsAlternating (A U))
    (hGood : ∀ a b, Good E a b ↔ ∀ U ∈ Rel E, U.Nonempty → ∃ c, A U a b c = 1) :
    5 * 2 ^ (2 * k) ≤ 32 * ((Finset.univ : Finset (S k × S k)).filter
      (fun v => @decide (Good E v.1 v.2) (Classical.propDecidable _))).card := by
  classical
  let I := (Rel E).erase ∅
  have hEmpty : (∅ : Finset (S k)) ∈ Rel E := by simp [Rel]
  have hI : I.card ≤ 3 := by
    have h := Finset.card_erase_add_one hEmpty
    change I.card + 1 = (Rel E).card at h
    omega
  have hmem (U : Finset (S k)) : U ∈ I ↔ U ∈ Rel E ∧ U.Nonempty := by
    simp only [I, Finset.mem_erase, Finset.nonempty_iff_ne_empty, and_comm]
  refine count_active I A hI ?_ (Good E) ?_
  · intro U hU
    obtain ⟨hm, hn⟩ := (hmem U).mp hU
    exact hA U hm hn
  · intro a b
    constructor
    · intro hg U hU
      obtain ⟨hm, hn⟩ := (hmem U).mp hU
      exact (active_iff (A U a b)).mp ((hGood a b).mp hg U hm hn)
    · intro ha
      apply (hGood a b).mpr
      intro U hU hn
      exact (active_iff (A U a b)).mpr (ha U ((hmem U).mpr ⟨hU, hn⟩))

end QL990.Counting

namespace QL990

lemma quantitative {k : ℕ} (E : Finset (S k)) (hE : (Rel E).card ≤ 4) :
    5 * 2 ^ (2 * k) ≤ 32 * ((Finset.univ : Finset (S k × S k)).filter
      (fun v => @decide (Good E v.1 v.2) (Classical.propDecidable _))).card := by
  refine Counting.count_good E (fun U => T U) hE ?_ ?_
  · intro U hU hn
    exact ⟨T_ne_zero hU hn hE, T_eq_zero₁₂ hU, T_eq_zero₁₃ hU, T_eq_zero₂₃ hU⟩
  · intro a b
    simpa only [T_apply] using good_iff E a b

end QL990

namespace QL990

private theorem pc_bit (x : F) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem pc_idem (x : F) : x * x = x := by
  rcases pc_bit x with rfl | rfl <;> simp

private theorem pc_qconst (r : F) : Quad (fun _ : S 4 => r) := by
  refine ⟨r, 0, 0, ?_⟩
  intro x
  simp [dotProduct]

private theorem pc_qdot (a : S 4) : Quad (dotProduct a) := by
  refine ⟨0, a, 0, ?_⟩
  intro x
  simp

private theorem pc_qprod (a b : S 4) : Quad (fun x => dotProduct a x * dotProduct b x) := by
  refine ⟨0, 0, fun i j => a i * b j, ?_⟩
  intro x
  simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem pc_qadd {f g : S 4 → F} (hf : Quad f) (hg : Quad g) :
    Quad (fun x => f x + g x) := by
  obtain ⟨b, l, M, hf⟩ := hf
  obtain ⟨b', l', M', hg⟩ := hg
  refine ⟨b+b', l+l', M+M', ?_⟩
  intro x
  simp only [hf, hg, dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private theorem pc_qscale {f : S 4 → F} (s : F) (hf : Quad f) :
    Quad (fun x => s * f x) := by
  obtain ⟨b, l, M, hf⟩ := hf
  refine ⟨s*b, fun i => s*l i, fun i j => s*M i j, ?_⟩
  intro x
  simp only [hf, dotProduct, mul_add, Finset.mul_sum, mul_assoc]

private theorem pc_qsum {ι : Type*} (T : Finset ι) (f : ι → S 4 → F)
    (hf : ∀ y ∈ T, Quad (f y)) : Quad (fun x => ∑ y ∈ T, f y x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using pc_qconst 0
  | @insert y T hy ih =>
    simpa only [Finset.sum_insert hy] using
      pc_qadd (hf y (Finset.mem_insert_self _ _))
        (ih (fun z hz => hf z (Finset.mem_insert_of_mem hz)))

private theorem pc_affine_three (p q r : F) (a b c : S 4) :
    ∃ g : S 4 → F, Quad g ∧ ∀ x,
      (p + dotProduct a x) * (q + dotProduct b x) * (r + dotProduct c x) =
        g x + triple a b c x := by
  refine ⟨fun x => p*q*r + (q*r)*dotProduct a x + (p*r)*dotProduct b x +
    (p*q)*dotProduct c x + r*(dotProduct a x * dotProduct b x) +
    q*(dotProduct a x * dotProduct c x) + p*(dotProduct b x * dotProduct c x), ?_, ?_⟩
  · exact pc_qadd (pc_qadd (pc_qadd (pc_qadd (pc_qadd (pc_qadd
      (pc_qconst (p*q*r)) (pc_qscale (q*r) (pc_qdot a)))
      (pc_qscale (p*r) (pc_qdot b))) (pc_qscale (p*q) (pc_qdot c)))
      (pc_qscale r (pc_qprod a b))) (pc_qscale q (pc_qprod a c)))
      (pc_qscale p (pc_qprod b c))
  · intro x
    unfold triple
    ring

private def pc_factor (i : Option (Fin 4)) (x : S 4) : F := i.elim 1 x

private def pc_pair (r : S 4 → F) : (S 4 → F) →ₗ[F] F where
  toFun f := ∑ x, r x * f x
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' t f := by
    simp only [RingHom.id_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)

private abbrev pc_moment (i : Option (Fin 4)) := pc_pair (pc_factor i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem pc_small_certificate : ∀ i j k : Option (Fin 4),
    (∑ x : S 4, pc_factor i x * (pc_factor j x * pc_factor k x)) = 0 := by
  decide

private theorem pc_qmoment {f : S 4 → F} (hf : Quad f) (i : Option (Fin 4)) :
    pc_moment i f = 0 := by
  obtain ⟨b, l, M, hf⟩ := hf
  change (∑ x : S 4, pc_factor i x * f x) = 0
  simp only [hf, dotProduct, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have h0 : (∑ x : S 4, pc_factor i x * b) = 0 := by
    simpa [pc_factor, mul_assoc, ← Finset.sum_mul] using
      congrArg (fun z : F => z * b) (pc_small_certificate i none none)
  have h1 (j : Fin 4) : (∑ x : S 4, pc_factor i x * (l j * x j)) = 0 := by
    calc
      _ = (∑ x : S 4, pc_factor i x * (pc_factor (some j) x * pc_factor none x)) * l j := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by simp only [pc_factor, Option.elim, mul_one]; ring)
      _ = 0 := by rw [pc_small_certificate, zero_mul]
  have h2 (j k : Fin 4) : (∑ x : S 4, pc_factor i x * (M j k * x j * x k)) = 0 := by
    calc
      _ = (∑ x : S 4, pc_factor i x * (pc_factor (some j) x * pc_factor (some k) x)) * M j k := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by simp only [pc_factor, Option.elim]; ring)
      _ = 0 := by rw [pc_small_certificate, zero_mul]
  have hl : (∑ x : S 4, ∑ j : Fin 4, pc_factor i x * (l j * x j)) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun j _ => h1 j)
  have hq : (∑ x : S 4, ∑ j : Fin 4, ∑ k : Fin 4,
      pc_factor i x * (M j k * x j * x k)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun k _ => h2 j k)
  simp only [h0, hl, hq, add_zero]

private def pc_delta (y x : S 4) : F := if x = y then 1 else 0

private theorem pc_pair_delta (r : S 4 → F) (y : S 4) : pc_pair r (pc_delta y) = r y := by
  change (∑ x : S 4, r x * (if x = y then 1 else 0)) = r y
  simp [mul_ite]

private theorem pc_delta_prod (y x : S 4) :
    pc_delta y x = ∏ i, (1 + y i + x i) := by
  classical
  by_cases h : x = y
  · subst x
    simp [pc_delta, add_assoc, CharTwo.add_self_eq_zero]
  · have he : ∃ j, x j ≠ y j := by
      by_contra! hh
      exact h (funext hh)
    obtain ⟨j, hj⟩ := he
    have hz : 1 + y j + x j = 0 := by
      rcases pc_bit (x j) with hx | hx <;> rcases pc_bit (y j) with hy | hy <;>
        rw [hx, hy] at hj ⊢ <;> first | contradiction | decide
    rw [pc_delta, if_neg h, Finset.prod_eq_zero (Finset.mem_univ j) hz]

private def pc_low (y : S 4) : S 4 → F := fun x =>
  let t := fun i : Fin 4 => 1 + y i
  t 0*t 1*t 2*t 3 +
    (t 1*t 2*t 3*x 0 + t 0*t 2*t 3*x 1 + t 0*t 1*t 3*x 2 + t 0*t 1*t 2*x 3) +
    ((t 2*t 3*x 0*x 1 + t 1*t 3*x 0*x 2 + t 1*t 2*x 0*x 3) +
      (t 0*t 3*x 1*x 2 + t 0*t 2*x 1*x 3) + t 0*t 1*x 2*x 3)

private theorem pc_low_quad (y : S 4) : Quad (pc_low y) := by
  let t := fun i : Fin 4 => 1 + y i
  refine ⟨t 0*t 1*t 2*t 3, ![t 1*t 2*t 3, t 0*t 2*t 3, t 0*t 1*t 3, t 0*t 1*t 2],
    ![![0, t 2*t 3, t 1*t 3, t 1*t 2], ![0, 0, t 0*t 3, t 0*t 2],
      ![0, 0, 0, t 0*t 1], ![0, 0, 0, 0]], ?_⟩
  intro x
  simp [pc_low, dotProduct, Fin.sum_univ_succ, t] <;> ring

private theorem pc_delta_expand (y x : S 4) :
    pc_delta y x = pc_low y x + x 0*x 1*x 2*x 3 +
      (1+y 0)*(x 1*x 2*x 3) + (1+y 1)*(x 0*x 2*x 3) +
      (1+y 2)*(x 0*x 1*x 3) + (1+y 3)*(x 0*x 1*x 2) := by
  rw [pc_delta_prod, Fin.prod_univ_four]
  unfold pc_low
  dsimp
  ring

private theorem pc_quad_of_moments {f : S 4 → F} (hf : ∀ i, pc_moment i f = 0) : Quad f := by
  have h0 : (∑ y : S 4, f y) = 0 := by
    simpa [pc_pair, pc_factor] using hf none
  have h1 (j : Fin 4) : (∑ y : S 4, f y * (1+y j)) = 0 := by
    have hj : (∑ y : S 4, f y * y j) = 0 := by
      simpa [pc_pair, pc_factor, mul_comm] using hf (some j)
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
    rw [h0, hj, add_zero]
  have hz (c : F) : (∑ y : S 4, f y * c) = 0 := by
    rw [← Finset.sum_mul, h0, zero_mul]
  have hc (j : Fin 4) (c : F) : (∑ y : S 4, f y * ((1+y j)*c)) = 0 := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, h1, zero_mul]
  have H : f = fun x => ∑ y : S 4, f y * pc_low y x := by
    funext x
    calc
      f x = ∑ y : S 4, f y * pc_delta y x := by
        simp [pc_delta, mul_ite]
      _ = ∑ y : S 4, f y * pc_low y x := by
        simp only [pc_delta_expand, mul_add, Finset.sum_add_distrib, hz, hc, add_zero]
  rw [H]
  exact pc_qsum _ _ (fun y _ => pc_qscale (f y) (pc_low_quad y))

private theorem pc_affine_orth (r : S 4 → F) (p : F) (l : S 4)
    (hr : ∀ x, r x = p + dotProduct l x) {f : S 4 → F} (hf : Quad f) :
    pc_pair r f = 0 := by
  have H0 : (∑ x : S 4, f x) = 0 := by
    simpa [pc_pair, pc_factor] using pc_qmoment hf none
  have H1 (j : Fin 4) : (∑ x : S 4, x j * f x) = 0 := by
    simpa [pc_pair, pc_factor] using pc_qmoment hf (some j)
  change (∑ x, r x * f x) = 0
  simp only [hr, dotProduct, add_mul, Finset.sum_mul, mul_assoc, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, H0, mul_zero, zero_add, Finset.sum_comm]
  exact Finset.sum_eq_zero (fun j _ => by rw [← Finset.mul_sum, H1, mul_zero])

private theorem pc_orth_affine (r : S 4 → F)
    (hr : ∀ f, Quad f → pc_pair r f = 0) :
    ∃ p : F, ∃ l : S 4, ∀ x, r x = p + dotProduct l x := by
  let e : Fin 4 → S 4 := fun j => Pi.single j 1
  refine ⟨r 0, fun j => r (e j) + r 0, ?_⟩
  intro x
  let D : S 4 → F := pc_delta x + (1 + ∑ j, x j) • pc_delta 0 +
    ∑ j : Fin 4, x j • pc_delta (e j)
  have hD : ∀ i, pc_moment i D = 0 := by
    intro i
    simp only [D, map_add, map_smul, map_sum, pc_pair_delta, smul_eq_mul]
    cases i with
    | none => simp [pc_factor, add_assoc, CharTwo.add_self_eq_zero]
    | some i => simp [pc_factor, e, Pi.single_apply, mul_ite, CharTwo.add_self_eq_zero]
  have hh := hr D (pc_quad_of_moments hD)
  simp only [D, map_add, map_smul, map_sum, pc_pair_delta, smul_eq_mul] at hh
  have hsum : dotProduct (fun j => r (e j) + r 0) x =
      (∑ j, x j * r (e j)) + (∑ j, x j) * r 0 := by
    simp only [dotProduct, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1 <;> exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  apply CharTwo.add_eq_zero.mp
  rw [hsum]
  linear_combination hh

private def pc_cube (u v : S 4) : Finset (S 4) := (Finset.univ.erase u).erase v

private theorem pc_mem_cube {u v x : S 4} : x ∈ pc_cube u v ↔ x ≠ u ∧ x ≠ v := by
  simp [pc_cube, and_comm]

private theorem pc_mem_rel {E U : Finset (S 4)} : U ∈ Rel E ↔
    U ⊆ E ∧ ∀ f, Quad f → (∑ x ∈ U, f x) = 0 := by
  classical
  simp only [Rel, Finset.mem_filter, Finset.mem_powerset, decide_eq_true_eq]

private noncomputable def pc_character (U : Finset (S 4)) (x : S 4) : F :=
  if x ∈ U then 1 else 0

private theorem pc_pair_character (U : Finset (S 4)) (f : S 4 → F) :
    pc_pair (pc_character U) f = ∑ x ∈ U, f x := by
  classical
  change (∑ x, (if x ∈ U then (1:F) else 0) * f x) = _
  simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  simp

private theorem pc_pivot {u v : S 4} (huv : u ≠ v) : ∃ i, v i + u i = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ u i := by
    by_contra! h
    exact huv (funext h).symm
  exact ⟨i, (pc_bit _).resolve_left (mt CharTwo.add_eq_zero.mp hi)⟩

private def pc_proj (u v : S 4) (i : Fin 4) (x : S 4) : S 4 :=
  x + u + (x i + u i) • (v + u)

private theorem pc_proj_i (u v : S 4) (i : Fin 4) (hi : v i + u i = 1) (x : S 4) :
    pc_proj u v i x i = 0 := by
  change x i + u i + (x i + u i) * (v i + u i) = 0
  rw [hi, mul_one, CharTwo.add_self_eq_zero]

private theorem pc_proj_eq_zero (u v : S 4) (i : Fin 4) (x : S 4) :
    pc_proj u v i x = 0 → x = u ∨ x = v := by
  intro h
  rcases pc_bit (x i + u i) with h0 | h1
  · left
    funext j
    exact CharTwo.add_eq_zero.mp (by simpa [pc_proj, h0] using congrFun h j)
  · right
    funext j
    apply CharTwo.add_eq_zero.mp
    have h' : x j + u j + (v j + u j) = 0 := by
      simpa only [pc_proj, Pi.add_apply, h1, one_smul, Pi.zero_apply] using congrFun h j
    linear_combination h' - CharTwo.add_self_eq_zero (u j)

private theorem pc_proj_u (u v : S 4) (i : Fin 4) : pc_proj u v i u = 0 := by
  funext j
  simp [pc_proj, CharTwo.add_self_eq_zero]

private theorem pc_proj_v (u v : S 4) (i : Fin 4) (hi : v i + u i = 1) :
    pc_proj u v i v = 0 := by
  funext j
  simp [pc_proj, hi, CharTwo.add_self_eq_zero]

private abbrev pc_indices (i : Fin 4) := {j : Fin 4 // j ≠ i}

private def pc_extend (i : Fin 4) (w : pc_indices i → F) : S 4 :=
  fun j => if h : j ≠ i then w ⟨j,h⟩ else 0

private def pc_weight (u v : S 4) (i : Fin 4) (w : pc_indices i → F) (x : S 4) : F :=
  dotProduct (pc_extend i w) (pc_proj u v i x)

private theorem pc_weight_aff (u v : S 4) (i : Fin 4) (w : pc_indices i → F) :
    ∃ p : F, ∃ l : S 4, ∀ x, pc_weight u v i w x = p + dotProduct l x := by
  let l := pc_extend i w
  let t := dotProduct l (v+u)
  refine ⟨dotProduct l u + t*u i, l + t • Pi.single i 1, ?_⟩
  intro x
  change dotProduct l (x + u + (x i + u i) • (v+u)) =
    dotProduct l u + t*u i + dotProduct (l + t • Pi.single i 1) x
  simp only [dotProduct_add, dotProduct_smul, add_dotProduct, smul_dotProduct,
    single_dotProduct, one_mul, smul_eq_mul, t]
  ring

private theorem pc_weight_basis (u v : S 4) (i : Fin 4) (w : pc_indices i → F)
    (j : pc_indices i) : pc_weight u v i w (u + Pi.single j.1 1) = w j := by
  have h : pc_proj u v i (u + Pi.single j.1 1) = Pi.single j.1 1 := by
    have hji : (Pi.single j.1 (1 : F) : S 4) i = 0 := by
      simp [Pi.single_apply, j.property, Ne.symm j.property]
    have h0 : u i + (Pi.single j.1 (1 : F) : S 4) i + u i = 0 := by
      simp [hji, CharTwo.add_self_eq_zero]
    funext k
    simp only [pc_proj, h0, zero_smul, Pi.add_apply, Pi.zero_apply, add_zero]
    linear_combination CharTwo.add_self_eq_zero (u k)
  rw [pc_weight, h]
  simp [pc_extend, j.property]

private theorem pc_weight_all (u v : S 4) (i : Fin 4) (hi : v i + u i = 1)
    (r : S 4 → F) (p : F) (l : S 4) (hr : ∀ x, r x = p + dotProduct l x)
    (hu : r u = 0) (hv : r v = 0) :
    r = pc_weight u v i (fun j => l j.1) := by
  have hp : p = dotProduct l u := CharTwo.add_eq_zero.mp ((hr u).symm.trans hu)
  have hz : dotProduct l (v+u) = 0 := by
    rw [dotProduct_add, CharTwo.add_eq_zero]
    exact (CharTwo.add_eq_zero.mp ((hr v).symm.trans hv)).symm.trans hp
  funext x
  rw [hr, hp, add_comm]
  calc
    dotProduct l x + dotProduct l u = dotProduct l (pc_proj u v i x) := by
      simp only [pc_proj, dotProduct_add, dotProduct_smul, hz, smul_zero, add_zero]
    _ = pc_weight u v i (fun j => l j.1) x := by
      unfold pc_weight dotProduct
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        rw [pc_proj_i u v i hi, mul_zero, mul_zero]
      · simp [pc_extend, hji]

private noncomputable def pc_support (u v : S 4) (i : Fin 4)
    (w : pc_indices i → F) : Finset (S 4) :=
  (pc_cube u v).filter (fun x => pc_weight u v i w x = 1)

private theorem pc_character_support (u v : S 4) (i : Fin 4) (hi : v i + u i = 1)
    (w : pc_indices i → F) : pc_character (pc_support u v i w) = pc_weight u v i w := by
  funext x
  rcases pc_bit (pc_weight u v i w x) with h | h
  · simp [pc_character, pc_support, h, zero_ne_one]
  · have hx : x ∈ pc_cube u v := by
      refine pc_mem_cube.mpr ⟨?_, ?_⟩
      · rintro rfl
        simp [pc_weight, pc_proj_u, zero_ne_one] at h
      · rintro rfl
        simp [pc_weight, pc_proj_v u x i hi] at h
    simp [pc_character, pc_support, hx, h]

private theorem pc_card_rel (u v : S 4) (huv : u ≠ v) : (Rel (pc_cube u v)).card = 8 := by
  classical
  obtain ⟨i, hi⟩ := pc_pivot huv
  let toRel (w : pc_indices i → F) : ↥(Rel (pc_cube u v)) :=
    ⟨pc_support u v i w, pc_mem_rel.mpr ⟨Finset.filter_subset _ _, by
      intro f hf
      rw [← pc_pair_character, pc_character_support u v i hi]
      obtain ⟨p, l, hl⟩ := pc_weight_aff u v i w
      exact pc_affine_orth _ p l hl hf⟩⟩
  have hInj : Function.Injective toRel := by
    intro w z h
    have hh := congrArg (fun U : ↥(Rel (pc_cube u v)) => pc_character U.val) h
    change pc_character (pc_support u v i w) = pc_character (pc_support u v i z) at hh
    rw [pc_character_support u v i hi, pc_character_support u v i hi] at hh
    funext j
    have he : pc_weight u v i w (u + Pi.single j.1 1) =
        pc_weight u v i z (u + Pi.single j.1 1) := congrFun hh _
    rwa [pc_weight_basis u v i w j, pc_weight_basis u v i z j] at he
  have hSurj : Function.Surjective toRel := by
    intro U
    obtain ⟨hsub, hann⟩ := pc_mem_rel.mp U.property
    obtain ⟨p, l, hl⟩ := pc_orth_affine (pc_character U.val) (by
      intro f hf
      rw [pc_pair_character]
      exact hann _ hf)
    have hu' : u ∉ U.val := fun h => (pc_mem_cube.mp (hsub h)).1 rfl
    have hv' : v ∉ U.val := fun h => (pc_mem_cube.mp (hsub h)).2 rfl
    have hu : pc_character U.val u = 0 := by simp [pc_character, hu']
    have hv : pc_character U.val v = 0 := by simp [pc_character, hv']
    refine ⟨fun j => l j.1, Subtype.ext ?_⟩
    have H := pc_weight_all u v i hi (pc_character U.val) p l hl hu hv
    change pc_support u v i (fun j => l j.1) = U.val
    ext x
    have he := congrFun H x
    rw [← pc_character_support u v i hi] at he
    have onSupport (T : Finset (S 4)) : pc_character T x = 1 ↔ x ∈ T := by
      by_cases h : x ∈ T <;> simp [pc_character, h, zero_ne_one]
    rw [← onSupport (pc_support u v i (fun j => l j.1)), ← onSupport U.val, he]
  rw [← Fintype.card_coe, ← Fintype.card_congr (Equiv.ofBijective toRel ⟨hInj,hSurj⟩), Fintype.card_fun]
  have hcard : Fintype.card (pc_indices i) = 3 := by
    rw [Fintype.card_subtype_compl (fun j => j = i), Fintype.card_subtype_eq, Fintype.card_fin]
  rw [hcard, ZMod.card]
  rfl

private theorem pc_line (d : S 4) :
    ∃ a b c : S 4, ∃ q : S 4 → F, Quad q ∧
      ∀ x, pc_delta 0 x + pc_delta d x = q x + triple a b c x := by
  classical
  by_cases hd : d = 0
  · subst d
    exact ⟨0, 0, 0, _, pc_qconst 0, by
      intro x
      simp [triple, CharTwo.add_self_eq_zero]⟩
  obtain ⟨i, hi⟩ := pc_pivot (Ne.symm hd)
  let L (j : Fin 4) : S 4 := Pi.single j 1 + d j • Pi.single i 1
  have hL (x : S 4) (j : Fin 4) : dotProduct (L j) x = pc_proj 0 d i x j := by
    simp [L, pc_proj, mul_comm]
  let J := (Finset.univ : Finset (Fin 4)).erase i
  have hc : J.card = 3 := by simp [J, Finset.card_erase_of_mem]
  obtain ⟨j,k,l,hjk,hjl,hkl,hJ⟩ := Finset.card_eq_three.mp hc
  obtain ⟨q,hq,hqeq⟩ := pc_affine_three 1 1 1 (L j) (L k) (L l)
  refine ⟨L j,L k,L l,q,hq,fun x => ?_⟩
  rw [← hqeq]
  have hprod : (∏ j ∈ J, (1 + pc_proj 0 d i x j)) =
      (1 + dotProduct (L j) x) * (1 + dotProduct (L k) x) * (1 + dotProduct (L l) x) := by
    rw [hJ]
    simp [hjk, hjl, hkl, hL, mul_assoc]
  rw [← hprod]
  by_cases hx : pc_proj 0 d i x = 0
  · rcases pc_proj_eq_zero 0 d i x hx with rfl | rfl <;>
      simp [hx, pc_delta, hd, Ne.symm hd]
  · have h0 : x ≠ 0 := by
      intro hz
      subst x
      exact hx (pc_proj_u 0 d i)
    have h1 : x ≠ d := by
      intro hz
      subst x
      exact hx (pc_proj_v 0 d i hi)
    obtain ⟨j, hj⟩ : ∃ j, pc_proj 0 d i x j ≠ 0 := by
      by_contra! h
      exact hx (funext h)
    have hji : j ≠ i := by
      intro hj'
      subst j
      exact hj (pc_proj_i 0 d i hi x)
    have hj' := (pc_bit _).resolve_left hj
    have hjJ : j ∈ J := by simp [J, hji]
    have hz : 1 + pc_proj 0 d i x j = 0 := by
      simpa only [hj'] using (CharTwo.add_self_eq_zero (1 : F))
    rw [Finset.prod_eq_zero hjJ hz]
    simp [pc_delta, h0, h1]

private theorem pc_per_offset (u v : S 4) (h : S 4 → F) :
    ∃ a b : S 4, Fit (pc_cube u v) a b h := by
  let h' := h + (pc_moment none h) • pc_delta u
  let d : S 4 := fun i => pc_moment (some i) h'
  obtain ⟨a,b,c,q,hq,hqeq⟩ := pc_line d
  let f := h' + (pc_delta 0 + pc_delta d)
  have hf : Quad f := pc_quad_of_moments (by
    intro i
    cases i with
    | none => simp [f, h', pc_pair_delta, pc_factor, CharTwo.add_self_eq_zero]
    | some i =>
      simp only [f, map_add, pc_pair_delta, pc_factor, Option.elim, Pi.zero_apply, zero_add]
      exact CharTwo.add_self_eq_zero (d i))
  refine ⟨a,b,c,fun x => f x + q x,pc_qadd hf hq,?_⟩
  intro x hx
  have hu := (pc_mem_cube.mp hx).1
  change h x = h x + pc_moment none h * pc_delta u x +
    (pc_delta 0 x + pc_delta d x) + q x + triple a b c x
  rw [hqeq]
  simp only [pc_delta, if_neg hu, mul_zero, add_zero]
  linear_combination -CharTwo.add_self_eq_zero (q x + triple a b c x)

private theorem pc_not_good_test (u v : S 4) (a b : S 4) (r : S 4 → F)
    (hu : r u = 0) (hv : r v = 0) (x : S 4) (hx : r x = 1)
    (hr : ∃ p : F, ∃ l : S 4, ∀ y, r y = p + dotProduct l y)
    (hc : ∀ c : S 4, ∃ q : S 4 → F, Quad q ∧
      ∀ y, r y = 1 → triple a b c y = q y) : ¬Good (pc_cube u v) a b := by
  intro hGood
  obtain ⟨c,f,hf,hfit⟩ := hGood (pc_delta x)
  obtain ⟨q,hq,hqeq⟩ := hc c
  obtain ⟨p,l,hl⟩ := hr
  have H : pc_pair r (pc_delta x) = pc_pair r (f + q) := by
    change (∑ y, r y * pc_delta x y) = ∑ y, r y * (f y + q y)
    apply Finset.sum_congr rfl
    intro y _
    rcases pc_bit (r y) with h | h
    · simp [h]
    · have hy : y ∈ pc_cube u v := pc_mem_cube.mpr ⟨by rintro rfl; simp [hu] at h,
        by rintro rfl; simp [hv] at h⟩
      rw [hfit y hy, hqeq y h]
  rw [pc_pair_delta, hx, map_add, pc_affine_orth r p l hl hf,
    pc_affine_orth r p l hl hq, add_zero] at H
  exact one_ne_zero H

private theorem pc_not_good (u v : S 4) (huv : u ≠ v) (a b : S 4) :
    ¬Good (pc_cube u v) a b := by
  have hDeg (h : ∀ c, Quad (triple a b c)) : ¬Good (pc_cube u v) a b := by
    obtain ⟨i, hi⟩ := pc_pivot huv
    obtain ⟨j,hj⟩ : ∃ j : Fin 4, j ≠ i := exists_ne i
    let w : pc_indices i → F := fun _ => 1
    refine pc_not_good_test u v a b (pc_weight u v i w) ?_ ?_ (u + Pi.single j 1)
      (pc_weight_basis u v i w ⟨j,hj⟩) (pc_weight_aff u v i w) ?_
    · simp [pc_weight, pc_proj_u]
    · simp [pc_weight, pc_proj_v u v i hi]
    · exact fun c => ⟨_,h c,fun _ _ => rfl⟩
  by_cases ha : a = 0
  · apply hDeg
    intro c
    rw [show triple a b c = fun _ => 0 from funext fun x => by simp [triple, ha]]
    exact pc_qconst 0
  by_cases hb : b = 0
  · apply hDeg
    intro c
    rw [show triple a b c = fun _ => 0 from funext fun x => by simp [triple, hb]]
    exact pc_qconst 0
  by_cases hab : a = b
  · apply hDeg
    intro c
    rw [show triple a b c = fun x => dotProduct b x * dotProduct c x from
      funext fun x => by simp [triple, hab, pc_idem]]
    exact pc_qprod b c
  have hTest (l : S 4) (hn : l ≠ 0) (hEq : dotProduct l u = dotProduct l v)
      (hc : ∀ c : S 4, ∃ q : S 4 → F, Quad q ∧ ∀ y,
        dotProduct l y = 1 + dotProduct l u → triple a b c y = q y) :
      ¬Good (pc_cube u v) a b := by
    obtain ⟨j,hj⟩ : ∃ j, l j = 1 := by
      by_contra! hh
      exact hn (funext fun j => (pc_bit _).resolve_right (hh j))
    let r : S 4 → F := fun y => dotProduct l u + dotProduct l y
    refine pc_not_good_test u v a b r ?_ ?_ (u + Pi.single j 1) ?_
      ⟨_,l,fun _ => rfl⟩ ?_
    · exact CharTwo.add_self_eq_zero _
    · exact CharTwo.add_eq_zero.mpr hEq
    · simp [r, hj, CharTwo.add_cancel_left]
    · intro c
      obtain ⟨q,hq,h⟩ := hc c
      refine ⟨q,hq,fun y hy => h y ?_⟩
      change dotProduct l u + dotProduct l y = 1 at hy
      rw [add_comm] at hy
      exact CharTwo.add_eq_iff_eq_add.mp hy
  by_cases hA : dotProduct a u = dotProduct a v
  · apply hTest a ha hA
    intro c
    refine ⟨fun x => (1 + dotProduct a u) * (dotProduct b x * dotProduct c x),
      pc_qscale _ (pc_qprod b c), ?_⟩
    intro x hx
    rw [triple, hx, mul_assoc]
  by_cases hB : dotProduct b u = dotProduct b v
  · apply hTest b hb hB
    intro c
    refine ⟨fun x => (1 + dotProduct b u) * (dotProduct a x * dotProduct c x),
      pc_qscale _ (pc_qprod a c), ?_⟩
    intro x hx
    rw [triple, hx]
    ring
  have hn : a+b ≠ 0 := by
    intro hz
    exact hab (funext fun j => CharTwo.add_eq_zero.mp (congrFun hz j))
  have hE : dotProduct (a+b) u = dotProduct (a+b) v := by
    have hA' := (pc_bit (dotProduct a u + dotProduct a v)).resolve_left
      (mt CharTwo.add_eq_zero.mp hA)
    have hB' := (pc_bit (dotProduct b u + dotProduct b v)).resolve_left
      (mt CharTwo.add_eq_zero.mp hB)
    apply CharTwo.add_eq_zero.mp
    rw [add_dotProduct, add_dotProduct,
      show dotProduct a u + dotProduct b u + (dotProduct a v + dotProduct b v) =
        (dotProduct a u + dotProduct a v) + (dotProduct b u + dotProduct b v) by ring,
      hA', hB'] <;> decide
  apply hTest (a+b) hn hE
  intro c
  let t := 1 + dotProduct (a+b) u
  refine ⟨fun x => (1+t) * (dotProduct a x * dotProduct c x),
    pc_qscale _ (pc_qprod a c), ?_⟩
  intro x hx
  change dotProduct (a+b) x = t at hx
  rw [add_dotProduct] at hx
  rw [triple, ← hx]
  rcases pc_bit (dotProduct a x) with hA | hA <;>
    rcases pc_bit (dotProduct b x) with hB | hB <;>
    simp [hA, hB, show (1:F)+1 = 0 by decide]

theorem pc_base (u v : S 4) (huv : u ≠ v) :
    let E := (((Finset.univ : Finset (S 4)).erase u).erase v)
    (Rel E).card = 8 ∧ (∀ h : S 4 → F, ∃ a b : S 4, Fit E a b h) ∧
      ¬∃ a b : S 4, Good E a b := by
  exact ⟨pc_card_rel u v huv, pc_per_offset u v, fun ⟨a,b,h⟩ => pc_not_good u v huv a b h⟩

end QL990

end PEqualNP.Outside.L_lib_990

open PEqualNP.Outside.L_lib_990 in
theorem PEqualNP.Outside.L_lib_990 : (∀ k : ℕ,
  let F := ZMod 2
  let S := Fin k → F
  let quad := fun (f : S → F) => ∃ (b : F) (l : S) (M : Fin k → Fin k → F),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
  let rel := fun (E : Finset S) => E.powerset.filter (fun U => @decide
    (∀ f : S → F, quad f → (∑ s ∈ U, f s) = 0) (Classical.propDecidable _))
  let triple := fun (a b c s : S) => dotProduct a s * dotProduct b s * dotProduct c s
  let fit := fun (E : Finset S) (a b : S) (h : S → F) =>
    ∃ (c : S) (f : S → F), quad f ∧ ∀ s ∈ E, h s = f s + triple a b c s
  let good := fun (E : Finset S) (a b : S) => ∀ h : S → F, fit E a b h
  (∀ E : Finset S,
    (∀ a b : S, good E a b ↔ ∀ U ∈ rel E, U.Nonempty →
      ∃ c : S, (∑ s ∈ U, triple a b c s) = 1) ∧
    ((rel E).card ≤ 4 →
      let pairs := (Finset.univ : Finset (S × S)).filter
        (fun v => @decide (good E v.1 v.2) (Classical.propDecidable _))
      5 * 2^(2*k) ≤ 32 * pairs.card)) ∧
  ∀ (B : (Fin 4 → F) →ₗ[F] S) (o : S) (u v : Fin 4 → F), Function.Injective B → u ≠ v →
    let E := (((Finset.univ : Finset (Fin 4 → F)).erase u).erase v).image (fun x => o+B x)
    (rel E).card = 8 ∧ (∀ h : S → F, ∃ a b : S, fit E a b h) ∧
    ¬∃ a b : S, good E a b) := by
  intro k
  dsimp only
  constructor
  · intro E
    exact ⟨fun a b => QL990.good_iff E a b, QL990.quantitative E⟩
  · intro B o u v hB huv
    exact QL990.affine_result B o ((Finset.univ.erase u).erase v) hB (QL990.pc_base u v huv)
