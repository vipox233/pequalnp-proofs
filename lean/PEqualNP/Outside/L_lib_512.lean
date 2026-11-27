import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_512

abbrev W (n : ℕ) := Fin n → Bool
abbrev Lit (n : ℕ) := Fin n × Bool
abbrev F (n : ℕ) := Finset (Lit n × Lit n)
def sat {n : ℕ} (A : F n) (w : W n) : Bool :=
  decide (∀ c ∈ A, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
def count {n : ℕ} (A : F n) : ℕ := (Finset.univ.filter fun u => sat A u = true).card
def covers {n : ℕ} (P : Finset (W n)) (r : ℕ) :=
  ∀ S : Finset (Fin n), S.card ≤ r → ∀ pat : W n, ∃ z ∈ P, ∀ bit ∈ S, z bit = pat bit
def learned {n : ℕ} (A : F n) (P : Finset (W n)) (x : W n) :=
  ∀ T : Finset (Fin n), T.card ≤ 2 → ∃ y ∈ P, sat A y = true ∧ ∀ j ∈ T, y j = x j

theorem learned_sat {n : ℕ} (A : F n) (P : Finset (W n)) (x : W n)
    (hx : learned A P x) : sat A x = true := by
  refine decide_eq_true ?_
  intro c hc
  have hcard : ({c.1.1,c.2.1} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  obtain ⟨y,_,hy,h⟩ := hx _ hcard
  have H := (of_decide_eq_true hy : ∀ v ∈ A, y v.1.1 ≠ v.1.2 ∨ y v.2.1 ≠ v.2.2) c hc
  simpa only [h _ (Finset.mem_insert_self ..),h _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))] using H

def cyl {n : ℕ} (S : Finset (Fin n)) (v : W n) : Finset (W n) :=
  Finset.univ.filter fun x => ∀ i ∈ S, x i = v i

theorem cardCyl {n : ℕ} (S : Finset (Fin n)) (v : W n) :
    (cyl S v).card = 2^(n - S.card) := by
  classical
  let e : ↥(cyl S v) ≃ ({i : Fin n // i ∉ S} → Bool) :=
    { toFun := fun x i => x.val i.val
      invFun := fun f => ⟨fun i => if hi : i ∈ S then v i else f ⟨i,hi⟩,
        by refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => ?_⟩; simp [hi]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · have h := (Finset.mem_filter.mp x.property).2 i hi
          simp [hi,h]
        · simp [hi]
      right_inv := by
        intro f
        funext i
        simp [i.property] }
  have hc := Fintype.card_subtype_compl (fun i : Fin n => i ∈ S)
  have hc' : Fintype.card {i : Fin n // i ∉ S} = n - S.card := by simpa using hc
  simpa [Fintype.card_fun,hc'] using Fintype.card_congr e

theorem starRecovery {n s : ℕ} (hs : 3 ≤ s) (hn : s < n) (P : Finset (W n))
    (cov : covers P (s+1)) (A : F n) (i : Fin n) (b : Bool) (L : Finset (Fin n))
    (v : W n) (hi : i ∉ L)
    (H : ∀ x : W n, sat A x = true ↔ x i ≠ b ∨ ∀ j ∈ L, x j = v j)
    (density : 2^n * (2^(s-1)+1) ≤ 2^s * count A)
    (x : W n) (hx : sat A x = true) : learned A P x := by
  classical
  let f : W n := fun j => if j = i then b else v j
  have sub : (Finset.univ.filter fun y : W n => sat A y = true) ⊆
      cyl {i} (fun _ => !b) ∪ cyl (insert i L) f := by
    intro y hy
    have hh := (H y).1 (Finset.mem_filter.mp hy).2
    by_cases h : y i = b
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · simpa [f] using h
      · simpa [f,ne_of_mem_of_not_mem hj hi] using (hh.resolve_left (not_not.mpr h)) j hj
    · apply Finset.mem_union_left
      have hh' : y i = !b := by cases b <;> cases h2 : y i <;> simp_all
      simpa [cyl] using hh'
  have hc : count A ≤ 2^(n-1)+2^(n-(L.card+1)) := by
    have z := (Finset.card_le_card sub).trans (Finset.card_union_le (cyl {i} (fun _ => !b)) (cyl (insert i L) f))
    simpa only [count,cardCyl,Finset.card_singleton,Finset.card_insert_of_notMem hi] using z
  have hsize : L.card+1 ≤ n := by
    have z := (Finset.card_le_univ (insert i L))
    simpa [hi] using z
  have hL : L.card < s := by
    by_contra! hbig
    have hprod : (2:ℕ)^s * 2^(n-1) = 2^n * 2^(s-1) := by
      rw [← pow_add,← pow_add]
      congr 1
      omega
    have hex : s + (n - (L.card+1)) < n := by omega
    have hsmall : (2:ℕ)^s * 2^(n-(L.card+1)) < 2^n := by
      rw [←pow_add]
      exact Nat.pow_lt_pow_right (by decide) hex
    have hh := density.trans (Nat.mul_le_mul_left (2^s) hc)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, hprod] at hh
    omega
  intro T hT
  by_cases h : x i = b
  · have hgood := ((H x).1 hx).resolve_left (not_not.mpr h)
    have hcard := Finset.card_union_le T L
    obtain ⟨y,hy,hy'⟩ := cov (T ∪ L) (by omega) x
    refine ⟨y,hy,(H y).2 (Or.inr ?_), fun j hj => hy' j (Finset.mem_union_left _ hj)⟩
    exact fun j hj => (hy' j (Finset.mem_union_right _ hj)).trans (hgood j hj)
  · have hcard := Finset.card_insert_le i T
    obtain ⟨y,hy,hy'⟩ := cov (insert i T) (by omega) x
    exact ⟨y,hy,(H y).2 (Or.inl (fun he => h ((hy' i (Finset.mem_insert_self ..)).symm.trans he))),
      fun j hj => hy' j (Finset.mem_insert_of_mem hj)⟩

theorem exists_accept_with_bit (n : ℕ) (A : F n) (hd : 2^n < 2*count A)
    (i : Fin n) (b : Bool) : ∃ x, sat A x = true ∧ x i = b := by
  classical
  by_contra! h
  have sub : (Finset.univ.filter fun y : W n => sat A y = true) ⊆ cyl {i} (fun _ => !b) := by
    intro y hy
    have hh := h y (Finset.mem_filter.mp hy).2
    have he : y i = !b := by cases b <;> cases h2 : y i <;> simp_all
    simpa [cyl] using he
  have hc : count A ≤ 2^(n-1) := by simpa [count,cardCyl] using Finset.card_le_card sub
  have he : 2*2^(n-1) = 2^n := by
    have hpos := i.isLt
    rw [←Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel (show 1 ≤ n by omega)]
  omega




def viol {n : ℕ} (x : W n) (D : Finset (Lit n)) := ∀ l ∈ D, x l.1 = l.2

private def edgeOf {n : ℕ} (p : Lit n × Lit n) : Finset (Lit n) := {p.1,p.2}
private noncomputable def edgesOf {n : ℕ} (A : F n) : Finset (Finset (Lit n)) := by
  classical
  exact (A.image edgeOf).filter (fun D => ∃ x : W n, viol x D)

private theorem sat_edges {n : ℕ} (A : F n) (x : W n) :
    sat A x = true ↔ ∀ D ∈ edgesOf A, ¬viol x D := by
  classical
  rw [sat,decide_eq_true_eq]
  constructor
  · intro h D hD hv
    obtain ⟨he,_⟩ := Finset.mem_filter.mp hD
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp he
    rcases h c hc with h1|h2
    · exact h1 (hv _ (Finset.mem_insert_self ..))
    · exact h2 (hv _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  · intro h c hc
    by_contra! hbad
    have hv : viol x (edgeOf c) := by
      intro l hl
      simp only [edgeOf,Finset.mem_insert,Finset.mem_singleton] at hl
      rcases hl with rfl|rfl
      · exact hbad.1
      · exact hbad.2
    exact h _ (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨c,hc,rfl⟩,x,hv⟩) hv

private lemma edgeDouble {n : ℕ} (A : F n)
    (bits : ∀ (i : Fin n) (b : Bool), ∃ x, sat A x = true ∧ x i = b)
    (D : Finset (Lit n)) (hD : D ∈ edgesOf A) : D.card = 2 := by
  classical
  obtain ⟨he,_⟩ := Finset.mem_filter.mp hD
  obtain ⟨⟨u,v⟩,hc,rfl⟩ := Finset.mem_image.mp he
  by_cases h : u = v
  · subst v
    obtain ⟨x,hx,hit⟩ := bits u.1 u.2
    have h := (of_decide_eq_true hx : ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2) _ hc
    exact False.elim ((h.elim id id) hit)
  · simp [edgeOf, h]

private theorem smallEdgesRecover {n s : ℕ} (hs : 3 ≤ s) (A : F n) (P : Finset (W n)) (hp : covers P (s+1))
    (hA : (edgesOf A).card ≤ 2) : ∀ x, sat A x = true → learned A P x := by
  classical
  intro x hx T hT
  have hu : ∀ D ∈ edgesOf A, ∃ l ∈ D, x l.1 ≠ l.2 := by
    intro D hD
    by_contra! hc
    exact (sat_edges A x).1 hx D hD hc
  choose lit mem ne using hu
  let keys := (edgesOf A).attach.image (fun D => (lit D.val D.property).1)
  have hkeys : keys.card ≤ 2 := by
    exact (Finset.card_image_le.trans (by simpa using hA))
  obtain ⟨z,hz,hv⟩ := hp (keys ∪ T) (by have := Finset.card_union_le keys T; omega) x
  refine ⟨z,hz,(sat_edges A z).2 ?_,fun j hj => hv _ (Finset.mem_union_right _ hj)⟩
  intro D hD hit
  let l := lit D hD
  have hkey : l.1 ∈ keys := Finset.mem_image.mpr ⟨⟨D,hD⟩,Finset.mem_attach _ _,rfl⟩
  have heq : z l.1 = x l.1 := hv _ (Finset.mem_union_left _ hkey)
  exact ne D hD (heq.symm.trans (hit l (mem D hD)))

private theorem pairRest {α : Type*} [DecidableEq α] {D : Finset α} {l : α}
    (hcard : D.card = 2) (hl : l ∈ D) : ∃ r ∈ D, r ≠ l ∧ D = {l,r} := by
  obtain ⟨i,j,hn,heq⟩ := Finset.card_eq_two.mp hcard
  subst D
  simp only [Finset.mem_insert,Finset.mem_singleton] at hl
  rcases hl with rfl|rfl
  · exact ⟨j,by simp,Ne.symm hn,rfl⟩
  · exact ⟨i,by simp,hn,Finset.pair_comm ..⟩

private theorem chooseCenter {α : Type*} [DecidableEq α] (𝒟 : Finset (Finset α))
    (many : 2 < 𝒟.card) (cards : ∀ D ∈ 𝒟, D.card = 2)
    (triple : ∀ D ∈ 𝒟, ∀ E ∈ 𝒟, ∀ H ∈ 𝒟, D ≠ E → D ≠ H → E ≠ H →
      ∃ l, l ∈ D ∧ l ∈ E ∧ l ∈ H) : ∃ l, ∀ D ∈ 𝒟, l ∈ D := by
  classical
  obtain ⟨D,hD,E,hE,hDE⟩ := Finset.one_lt_card.mp (by omega : 1 < 𝒟.card)
  have hex : ∃ H ∈ 𝒟, D ≠ H ∧ E ≠ H := by
    by_contra! h
    have hsub : 𝒟 ⊆ {D,E} := by
      intro H hH
      by_cases h1 : D=H
      · simp [h1]
      · simp [←h H hH h1]
    exact (not_le.mpr many) ((Finset.card_le_card hsub).trans Finset.card_le_two)
  obtain ⟨H,hH,h1,h2⟩ := hex
  obtain ⟨l,hlD,hlE,hlH⟩ := triple D hD E hE H hH hDE h1 h2
  have uniqueL (v : α) (hvD : v ∈ D) (hvE : v ∈ E) : v = l := by
    by_contra h
    have two : ({v,l} : Finset α).card = 2 := by simp [h]
    have subD : ({v,l} : Finset α) ⊆ D := Finset.insert_subset hvD (Finset.singleton_subset_iff.mpr hlD)
    have subE : ({v,l} : Finset α) ⊆ E := Finset.insert_subset hvE (Finset.singleton_subset_iff.mpr hlE)
    have h1 := Finset.eq_of_subset_of_card_le subD (le_of_eq ((cards D hD).trans two.symm))
    have h2 := Finset.eq_of_subset_of_card_le subE (le_of_eq ((cards E hE).trans two.symm))
    exact hDE (h1.symm.trans h2)
  refine ⟨l,?_⟩
  intro J hJ
  by_cases hd : D = J
  · simpa [←hd] using hlD
  by_cases he : E = J
  · simpa [←he] using hlE
  obtain ⟨v,hv,hv',hJ'⟩ := triple D hD E hE J hJ hDE hd he
  simpa [uniqueL v hv hv'] using hJ'

private theorem starFromCenter {n : ℕ} (A : F n) (c : Lit n)
    (bits : ∀ (i : Fin n) (b : Bool), ∃ x, sat A x = true ∧ x i = b)
    (center : ∀ D ∈ edgesOf A, c ∈ D) :
    ∃ (L : Finset (Fin n)) (f : W n), c.1 ∉ L ∧
      ∀ x, sat A x = true ↔ x c.1 ≠ c.2 ∨ ∀ j ∈ L, x j = f j := by
  classical
  obtain ⟨f,hf,hfC⟩ := bits c.1 c.2
  let rest := ((edgesOf A).biUnion id).erase c
  let L := rest.image Prod.fst
  have hmem {v : Lit n} : v ∈ rest ↔ v ≠ c ∧ ∃ D ∈ edgesOf A, v ∈ D := by
    simp [rest]
  have secondNe {D : Finset (Lit n)} (hD : D ∈ edgesOf A) {v : Lit n} (hv : v ∈ D) (hvc : v ≠ c)
      {x : W n} (hx : sat A x = true) (hcx : x c.1 = c.2) : x v.1 ≠ v.2 := by
    obtain ⟨l,_,hl,heq⟩ := pairRest (edgeDouble A bits D hD) (center D hD)
    have hvl : v = l := by simpa [heq,hvc] using hv
    intro hh
    apply (sat_edges A x).1 hx D hD
    intro t ht
    simp only [heq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl|rfl
    · exact hcx
    · simpa [hvl] using hh
  refine ⟨L,f,?_,?_⟩
  · intro hh
    obtain ⟨v,hv,hv'⟩ := Finset.mem_image.mp hh
    obtain ⟨hne,D,hD,hm⟩ := hmem.mp hv
    obtain ⟨z,hz⟩ := (Finset.mem_filter.mp hD).2
    exact hne (Prod.ext hv' (by rw [←hz v hm,←hz c (center D hD),hv']))
  intro x
  constructor
  · intro hx
    by_cases hc : x c.1 = c.2
    · right
      intro j hj
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hne,D,hD,hm⟩ := hmem.mp hv
      have h1 := secondNe hD hm hne hx hc
      have h2 := secondNe hD hm hne hf hfC
      have hb : ∀ u v b : Bool, u ≠ b → v ≠ b → u = v := by decide
      exact hb _ _ _ h1 h2
    · exact Or.inl hc
  · intro hh
    apply (sat_edges A x).2
    intro D hD bad
    obtain ⟨v,hv,hne,_⟩ := pairRest (edgeDouble A bits D hD) (center D hD)
    rcases hh with h1|h2
    · exact h1 (bad _ (center D hD))
    · have hin : v.1 ∈ L := Finset.mem_image.mpr ⟨v,hmem.mpr ⟨hne,D,hD,hv⟩,rfl⟩
      exact secondNe hD hv hne hf hfC ((h2 _ hin).symm.trans (bad _ hv))
theorem recoveryFromObstruction {n s : ℕ} (hs : 3 ≤ s) (A : F n) (P : Finset (W n))
    (hp : covers P (s+1)) (hd : 2^n < 2*count A)
    (bits : ∀ (i : Fin n) (b : Bool), ∃ x, sat A x = true ∧ x i = b)
    (hstar : ∀ (i : Fin n) (b : Bool) (L : Finset (Fin n)) (f : W n), i ∉ L →
      (∀ x, sat A x = true ↔ x i ≠ b ∨ ∀ j ∈ L, x j = f j) →
      ∀ x, sat A x = true → learned A P x)
    (obstruct : ∀ (D E H : Finset (Lit n)), D ≠ E → D ≠ H → E ≠ H →
      D.card = 2 → E.card = 2 → H.card = 2 →
      (∃ x, viol x D) → (∃ x, viol x E) → (∃ x, viol x H) →
      (¬ ∃ l, l ∈ D ∧ l ∈ E ∧ l ∈ H) →
      (∀ x, sat A x = true → ¬viol x D ∧ ¬viol x E ∧ ¬viol x H) → 2*count A ≤ 2^n) :
    ∀ x, sat A x = true → learned A P x := by
  classical
  by_cases hsml : (edgesOf A).card ≤ 2
  · exact smallEdgesRecover hs A P hp hsml
  obtain ⟨c,hc⟩ : ∃ c, ∀ D ∈ edgesOf A, c ∈ D := by
    apply chooseCenter (edgesOf A) (by omega) (edgeDouble A bits)
    intro D hD E hE H hH dE dH eH
    by_contra h
    apply (not_le.mpr hd)
    apply obstruct D E H dE dH eH (edgeDouble A bits D hD) (edgeDouble A bits E hE)
      (edgeDouble A bits H hH) (Finset.mem_filter.mp hD).2 (Finset.mem_filter.mp hE).2
      (Finset.mem_filter.mp hH).2 h
    exact fun x hx => ⟨(sat_edges A x).1 hx _ hD,(sat_edges A x).1 hx _ hE,(sat_edges A x).1 hx _ hH⟩
  obtain ⟨L,f,hi,eqv⟩ := starFromCenter A c bits hc
  exact hstar c.1 c.2 L f hi eqv





noncomputable def fobsCylinder {n : ℕ} (D : Finset (Lit n)) : Finset (W n) := by
  classical exact Finset.univ.filter fun x => viol x D

theorem fobs_mem {n} (D : Finset (Lit n)) (x : W n) :
    x ∈ fobsCylinder D ↔ viol x D := by classical simp [fobsCylinder]

theorem fobs_meet {n} (D E : Finset (Lit n)) :
    fobsCylinder (D ∪ E) = fobsCylinder D ∩ fobsCylinder E := by
  classical
  ext x
  rw [fobs_mem,Finset.mem_inter,fobs_mem,fobs_mem]
  exact Finset.forall_mem_union

theorem fobs_size {n} (D : Finset (Lit n)) (att : ∃ w, viol w D) :
    2 ^ D.card * (fobsCylinder D).card = 2 ^ n := by
  classical
  obtain ⟨w, hw⟩ := att
  let I := D.image Prod.fst
  have hI : I.card = D.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy h
    exact Prod.ext h ((hw x hx).symm.trans ((congrArg w h).trans (hw y hy)))
  have rep : fobsCylinder D = Fintype.piFinset
      (fun i : Fin n => if i ∈ I then {w i} else Finset.univ) := by
    ext x
    rw [fobs_mem, Fintype.mem_piFinset]
    constructor
    · intro hx i
      by_cases hi : i ∈ I
      · obtain ⟨l,hl,he⟩ := Finset.mem_image.mp hi
        subst i
        simpa [hi] using (hx l hl).trans (hw l hl).symm
      · simp [hi]
    · intro hx l hl
      have hi : l.1 ∈ I := Finset.mem_image.mpr ⟨l,hl,rfl⟩
      have hh : x l.1 = w l.1 := by simpa [hi] using hx l.1
      exact hh.trans (hw l hl)
  rw [rep, Fintype.card_piFinset]
  have factors : (∏ i : Fin n, (if i ∈ I then {w i} else (Finset.univ : Finset Bool)).card) =
      ∏ i : Fin n, (if i ∈ I then 1 else 2) := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : i ∈ I <;> simp [h]
  rw [factors, Finset.prod_ite]
  have comp : (Finset.univ.filter fun i : Fin n => i ∉ I) = Iᶜ := by ext; simp
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const, comp, ← pow_add]
  congr 1
  rw [← hI]
  simpa using Finset.card_add_card_compl I

theorem fobs_le {n} (D : Finset (Lit n)) {k : ℕ} (h : k ≤ D.card) :
    2 ^ k * (fobsCylinder D).card ≤ 2 ^ n := by
  classical
  by_cases ex : ∃ x, viol x D
  · rw [← fobs_size D ex]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h)
  · have zero : fobsCylinder D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact ex ⟨x, (fobs_mem D x).mp hx⟩
    simp [zero]

theorem fobs_pair_bound {n} (D E : Finset (Lit n)) (d : D.card = 2)
    (e : E.card = 2) (ne : D ≠ E) :
    8 * (fobsCylinder D ∩ fobsCylinder E).card ≤ 2^n := by
  rw [← fobs_meet]
  apply fobs_le (k:=3)
  by_contra! hh
  have hD : D = D ∪ E := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have hE : E = D ∪ E := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  exact ne (hD.trans hE.symm)

theorem fobs_disj_bound {n} (D E : Finset (Lit n)) (d : D.card = 2)
    (e : E.card = 2) (disj : Disjoint D E) :
    16 * (fobsCylinder D ∩ fobsCylinder E).card ≤ 2^n := by
  rw [← fobs_meet]
  apply fobs_le (k:=4)
  rw [Finset.card_union_of_disjoint disj,d,e]

theorem fobs_contained {n} {D E H : Finset (Lit n)} (d : D.card = 2)
    (de : ¬ Disjoint D E) (dh : ¬ Disjoint D H)
    (nocommon : ¬ ∃ l, l ∈ D ∧ l ∈ E ∧ l ∈ H) : D ⊆ E ∪ H := by
  classical
  obtain ⟨a,ha,ae⟩ := Finset.not_disjoint_iff.mp de
  obtain ⟨b,hb,bh⟩ := Finset.not_disjoint_iff.mp dh
  have neq : a ≠ b := by rintro rfl; exact nocommon ⟨a,ha,ae,bh⟩
  have sub : ({a,b} : Finset (Lit n)) ⊆ D := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl <;> assumption
  have eq : {a,b} = D := Finset.eq_of_subset_of_card_le sub (by simp [neq,d])
  rw [←eq]
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl|rfl
  · exact Finset.mem_union_left _ ae
  · exact Finset.mem_union_right _ bh

theorem fobs_middle {n} {D E H : Finset (Lit n)} (sub : D ⊆ E ∪ H) :
    ((fobsCylinder D ∪ fobsCylinder E) ∩ fobsCylinder H) = fobsCylinder D ∩ fobsCylinder H := by
  classical
  have contained : fobsCylinder E ∩ fobsCylinder H ⊆ fobsCylinder D := by
    intro x hx; rw [fobs_mem]; intro l hl
    rcases Finset.mem_union.mp (sub hl) with he | hh
    · exact ((fobs_mem E x).mp (Finset.mem_inter.mp hx).1) l he
    · exact ((fobs_mem H x).mp (Finset.mem_inter.mp hx).2) l hh
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h,hx⟩
    exact ⟨h.elim id (fun he => contained (Finset.mem_inter.mpr ⟨he,hx⟩)),hx⟩
  · rintro ⟨h,hx⟩
    exact ⟨Or.inl h,hx⟩


theorem fobs_pay_middle {n} (D E H : Finset (Lit n))
    (hd : D.card=2) (he : E.card=2) (hh : H.card=2)
    (de : D≠E) (dh : D≠H) (sub : D ⊆ E∪H)
    (dV : ∃ x, viol x D) (eV : ∃ x, viol x E) (hV : ∃ x, viol x H) :
    2^n ≤ 2 * ((fobsCylinder D ∪ fobsCylinder E) ∪ fobsCylinder H).card := by
  classical
  have pd := fobs_size D dV
  have pe := fobs_size E eV
  have ph := fobs_size H hV
  rw [hd] at pd; rw [he] at pe; rw [hh] at ph
  have pde := fobs_pair_bound D E hd he de
  have pdh := fobs_pair_bound D H hd hh dh
  have m₁ := Finset.card_union_add_card_inter (fobsCylinder D) (fobsCylinder E)
  have m₂ := Finset.card_union_add_card_inter (fobsCylinder D ∪ fobsCylinder E) (fobsCylinder H)
  rw [fobs_middle sub] at m₂
  omega

theorem fobs_pay_rest {n} (D E H : Finset (Lit n))
    (hd : D.card=2) (he : E.card=2) (hh : H.card=2)
    (de : D≠E) (dh : D≠H) (eh : E≠H)
    (dis : (Disjoint D E ∧ Disjoint D H) ∨ (Disjoint D E ∧ Disjoint E H)
       ∨ (Disjoint D H ∧ Disjoint E H))
    (dV : ∃ x, viol x D) (eV : ∃ x, viol x E) (hV : ∃ x, viol x H) :
    2^n ≤ 2 * ((fobsCylinder D ∪ fobsCylinder E) ∪ fobsCylinder H).card := by
  classical
  have pd := fobs_size D dV
  have pe := fobs_size E eV
  have ph := fobs_size H hV
  rw [hd] at pd; rw [he] at pe; rw [hh] at ph
  have m₁ := Finset.card_union_add_card_inter (fobsCylinder D) (fobsCylinder E)
  have m₂ := Finset.card_union_add_card_inter (fobsCylinder D ∪ fobsCylinder E) (fobsCylinder H)
  rw [Finset.union_inter_distrib_right] at m₂
  have m₃ := Finset.card_union_le (fobsCylinder D ∩ fobsCylinder H) (fobsCylinder E ∩ fobsCylinder H)
  rcases dis with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
  · have x := fobs_disj_bound D E hd he a
    have y := fobs_disj_bound D H hd hh b
    have z := fobs_pair_bound E H he hh eh
    omega
  · have x := fobs_disj_bound D E hd he a
    have y := fobs_pair_bound D H hd hh dh
    have z := fobs_disj_bound E H he hh b
    omega
  · have x := fobs_pair_bound D E hd he de
    have y := fobs_disj_bound D H hd hh a
    have z := fobs_disj_bound E H he hh b
    omega

theorem clauseObstruction {n : ℕ} (A : F n) (D E H : Finset (Lit n))
    (hd : D.card=2) (he : E.card=2) (hh : H.card=2)
    (de : D≠E) (dh : D≠H) (eh : E≠H)
    (dV : ∃ x, viol x D) (eV : ∃ x, viol x E) (hV : ∃ x, viol x H)
    (nc : ¬ ∃ l, l∈D ∧ l∈E ∧ l∈H)
    (forbid : ∀ x, sat A x = true → ¬viol x D ∧ ¬viol x E ∧ ¬viol x H) :
    2 * count A ≤ 2^n := by
  classical
  have pay : 2^n ≤ 2 * ((fobsCylinder D ∪ fobsCylinder E) ∪ fobsCylinder H).card := by
    by_cases d₁ : Disjoint D E <;> by_cases d₂ : Disjoint D H
    · exact fobs_pay_rest D E H hd he hh de dh eh (Or.inl ⟨d₁,d₂⟩) dV eV hV
    · by_cases d₃ : Disjoint E H
      · exact fobs_pay_rest D E H hd he hh de dh eh (Or.inr (Or.inl ⟨d₁,d₃⟩)) dV eV hV
      · have c := fobs_contained hh (fun h => d₂ h.symm) (fun h => d₃ h.symm)
            (show ¬ ∃ l, l ∈ H ∧ l ∈ D ∧ l ∈ E by
              rintro ⟨l,lh,ld,le⟩; exact nc ⟨l,ld,le,lh⟩)
        simpa only [Finset.union_assoc,Finset.union_left_comm,Finset.union_comm] using
          fobs_pay_middle H D E hh hd he (Ne.symm dh) (Ne.symm eh) c hV dV eV
    · by_cases d₃ : Disjoint E H
      · exact fobs_pay_rest D E H hd he hh de dh eh (Or.inr (Or.inr ⟨d₂,d₃⟩)) dV eV hV
      · have c := fobs_contained he (fun h => d₁ h.symm) d₃
            (show ¬ ∃ l, l ∈ E ∧ l ∈ D ∧ l ∈ H by
              rintro ⟨l,le,ld,lh⟩; exact nc ⟨l,ld,le,lh⟩)
        simpa only [Finset.union_assoc,Finset.union_left_comm,Finset.union_comm] using
          fobs_pay_middle E D H he hd hh (Ne.symm de) eh c eV dV hV
    · exact fobs_pay_middle D E H hd he hh de dh (fobs_contained hd d₁ d₂ nc) dV eV hV
  let good := Finset.univ.filter fun x : W n => sat A x = true
  let bad := (fobsCylinder D ∪ fobsCylinder E) ∪ fobsCylinder H
  have disj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a,b,c⟩ := forbid x (Finset.mem_filter.mp hx).2
    rcases Finset.mem_union.mp hy with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact a ((fobs_mem D x).mp h)
      · exact b ((fobs_mem E x).mp h)
    · exact c ((fobs_mem H x).mp h)
  have together := Finset.card_le_univ (good ∪ bad)
  rw [Finset.card_union_of_disjoint disj] at together
  have total : Fintype.card (W n) = 2^n := by simp [W,Fintype.card_pi]
  rw [total] at together
  change count A + bad.card ≤ 2 ^ n at together
  change 2^n ≤ 2*bad.card at pay
  omega




private abbrev SW (n : ℕ) := Fin n → Bool
private abbrev SC (n : ℕ) := Finset ((Fin n × Bool) × (Fin n × Bool))
private def sharpSat {n : ℕ} (C : SC n) (w : SW n) : Bool :=
  decide (∀ e ∈ C, w e.1.1 ≠ e.1.2 ∨ w e.2.1 ≠ e.2.2)
private def sharpCount {n : ℕ} (C : SC n) := (Finset.univ.filter (fun w => sharpSat C w=true)).card
private def sharpStar {n : ℕ} (G : Finset (Fin n)) (c : Fin n) : SC n :=
  G.image (fun i => ((c,false),(i,true)))
private def sharpFixed {n : ℕ} (G : Finset (Fin n)) (b : Bool) : Finset (SW n) :=
  Finset.univ.filter fun w => ∀ i ∈ G, w i = b
private def sharpOnes {n : ℕ} (G : Finset (Fin n)) (w : SW n) := G.filter fun i => w i = true
private def sharpPool {n : ℕ} (G : Finset (Fin n)) : Finset (SW n) :=
  Finset.univ.filter fun w => (sharpOnes G w).card % 2 = 0
private def sharpFlip {n : ℕ} (i : Fin n) (w : SW n) : SW n := Function.update w i (!(w i))

private theorem sharpStar_iff {n : ℕ} (G : Finset (Fin n)) (c : Fin n) (w : SW n) :
    sharpSat (sharpStar G c) w = true ↔ w c = true ∨ ∀ i ∈ G, w i = false := by
  cases h : w c <;> simp [sharpSat,sharpStar,h]

private theorem sharpFixCard {n : ℕ} (G : Finset (Fin n)) (b : Bool) :
    (sharpFixed G b).card = 2^(n-G.card) := by
  classical
  let e : ↥(sharpFixed G b) ≃ (↥(Gᶜ) → Bool) :=
    { toFun := fun w i => w.val i.val
      invFun := fun f => ⟨fun i => if h : i ∈ G then b else f ⟨i,Finset.mem_compl.mpr h⟩, by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i hi => dif_pos hi⟩⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ G
        · simpa [hi] using ((Finset.mem_filter.mp w.property).2 i hi).symm
        · simp [hi]
      right_inv := by
        intro f
        funext i
        simp [Finset.mem_compl.mp i.property] }
  simpa [Fintype.card_fun,Finset.card_compl] using Fintype.card_congr e

private theorem sharpStarCount {n : ℕ} (G : Finset (Fin n)) (c : Fin n) (hc : c ∈ G) :
    sharpCount (sharpStar G c) = 2^(n-1)+2^(n-G.card) := by
  classical
  have he : Finset.univ.filter (fun w => sharpSat (sharpStar G c) w=true) =
      sharpFixed {c} true ∪ sharpFixed G false := by
    ext w
    simp [sharpStar_iff,sharpFixed]
  have hd : Disjoint (sharpFixed {c} true) (sharpFixed G false) := by
    apply Finset.disjoint_left.mpr
    intro w h1 h2
    have e1 : w c = true := by simpa [sharpFixed] using h1
    have e2 := (Finset.mem_filter.mp h2).2 c hc
    simp [e1] at e2
  unfold sharpCount
  rw [he,Finset.card_union_of_disjoint hd,sharpFixCard,sharpFixCard]
  simp

private theorem sharpFlipFlip {n : ℕ} (i : Fin n) (w : SW n) : sharpFlip i (sharpFlip i w) = w := by
  funext j
  by_cases h : j=i
  · subst j; simp [sharpFlip]
  · simp [sharpFlip,h]

private theorem sharpFlipMem {n : ℕ} {G : Finset (Fin n)} {i : Fin n} (hi : i∈G) (w : SW n) :
    sharpFlip i w ∈ sharpPool G ↔ w ∉ sharpPool G := by
  classical
  simp only [sharpPool,Finset.mem_filter,Finset.mem_univ,true_and]
  cases hw : w i with
  | false =>
    have hh : sharpOnes G (sharpFlip i w) = insert i (sharpOnes G w) := by
      ext j
      by_cases h : j=i
      · subst j; simp [sharpOnes, sharpFlip, hw, hi]
      · have hm (z : SW n) : j ∈ sharpOnes G z ↔ j∈G ∧ z j = true := Finset.mem_filter
        rw [hm (sharpFlip i w),Finset.mem_insert,hm w]
        simp [sharpFlip,h]
    have hm : i∉sharpOnes G w := by simp [sharpOnes,hw]
    rw [hh,Finset.card_insert_of_notMem hm]
    omega
  | true =>
    have hh : sharpOnes G (sharpFlip i w) = (sharpOnes G w).erase i := by
      ext j
      by_cases h : j=i
      · subst j; simp [sharpOnes,sharpFlip,hw]
      · have hm (z : SW n) : j ∈ sharpOnes G z ↔ j∈G ∧ z j = true := Finset.mem_filter
        rw [hm (sharpFlip i w),Finset.mem_erase,hm w]
        simp [sharpFlip,h]
    have hm : i∈sharpOnes G w := by simp [sharpOnes,hw,hi]
    have hp := Finset.card_pos.mpr ⟨i,hm⟩
    rw [hh,Finset.card_erase_of_mem hm]
    omega

private theorem sharpPoolCard {n : ℕ} {G : Finset (Fin n)} {i : Fin n} (hi : i∈G) :
    2*(sharpPool G).card=2^n := by
  classical
  let P := sharpPool G
  let e : ↥P ≃ ↥(Pᶜ) :=
    { toFun := fun w => ⟨sharpFlip i w.val, Finset.mem_compl.mpr (fun h => (sharpFlipMem hi _).mp h w.property)⟩
      invFun := fun z => ⟨sharpFlip i z.val,(sharpFlipMem hi _).mpr (Finset.mem_compl.mp z.property)⟩
      left_inv := fun _ => Subtype.ext (sharpFlipFlip _ _)
      right_inv := fun _ => Subtype.ext (sharpFlipFlip _ _) }
  have eq : P.card=(Pᶜ).card := by simpa only [Fintype.card_coe] using Fintype.card_congr e
  have hsum := P.card_add_card_compl
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hsum
  change 2 * P.card = _
  omega

private theorem sharpPoolCovers {n : ℕ} {G S : Finset (Fin n)} (hs : S.card<G.card) (w : SW n) :
    ∃ z ∈ sharpPool G, ∀ i∈S, z i = w i := by
  classical
  by_cases hw : w ∈ sharpPool G
  · exact ⟨w, hw, fun _ _ => rfl⟩
  have hn : ¬G⊆S := fun h => (Nat.not_le_of_gt hs) (Finset.card_le_card h)
  obtain ⟨j,hj,hns⟩ := Finset.not_subset.mp hn
  refine ⟨sharpFlip j w,(sharpFlipMem hj w).mpr hw,fun i hi => ?_⟩
  have h : i≠j := fun e => hns (e ▸ hi)
  simp [sharpFlip,h]

private theorem sharpErasePool {n : ℕ} (G : Finset (Fin n)) (r : Fin n) (hr : r∈G) (w : SW n)
    (hp : w∈sharpPool G) : (∀ i∈G.erase r,w i=false) ↔ ∀ i∈G,w i=false := by
  constructor
  · intro h i hi
    by_cases hir : i=r
    · subst i
      cases hw : w r with
      | false => rfl
      | true =>
        have hh : sharpOnes G w = {r} := by
          ext j
          by_cases hj : j=r
          · subst j; simp [sharpOnes,hr,hw]
          · by_cases hg : j∈G
            · have hz := h j (Finset.mem_erase.mpr ⟨hj,hg⟩)
              simp [sharpOnes,hj,hz]
            · simp [sharpOnes,hj,hg]
        have want := (Finset.mem_filter.mp hp).2
        simp [hh] at want
    · exact h i (Finset.mem_erase.mpr ⟨hir,hi⟩)
  · exact fun h i hi => h i (Finset.mem_of_mem_erase hi)

theorem fridaySharp (n s : ℕ) (hs : 3 ≤ s) (hsn : s < n) :
    ∃ (pool : Finset (SW n)) (A B : SC n),
      (∀ S : Finset (Fin n), S.card ≤ s → ∀ pat : SW n, ∃ z ∈ pool, ∀ j ∈ S, z j = pat j) ∧
      2*pool.card = 2^n ∧ 2^s*sharpCount A = 2^n*(2^(s-1)+1) ∧
      sharpCount B = sharpCount A ∧ (∀ w ∈ pool, sharpSat A w = sharpSat B w) ∧
      ∃ w, sharpSat A w ≠ sharpSat B w := by
  classical
  let f : Fin (s+1) → Fin n := Fin.castLE (by omega)
  let U := Finset.univ.image f
  have hf : Function.Injective f := by intro i j h; exact Fin.ext (congrArg (fun p : Fin n => p.val) h)
  have cardU : U.card = s+1 := by simp [U, Finset.card_image_of_injective _ hf]
  let c : Fin n := ⟨0,by omega⟩
  let l : Fin n := ⟨s-1,by omega⟩
  let r : Fin n := ⟨s,hsn⟩
  have mem (k : Fin n) (hk : k.val ≤ s) : k∈U :=
    Finset.mem_image.mpr ⟨⟨k.val,by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
  have hc : c∈U := mem _ (Nat.zero_le _)
  have hl : l∈U := mem _ (Nat.sub_le _ _)
  have hr : r∈U := mem _ (le_refl _)
  have hcr : c ≠ r := fun e => by have h := congrArg Fin.val e; change 0=s at h; omega
  have hcl : c ≠ l := fun e => by have h := congrArg Fin.val e; change 0=s-1 at h; omega
  have hrl : r ≠ l := fun e => by have h := congrArg Fin.val e; change s=s-1 at h; omega
  have ct (j : Fin n) (hj : j∈U) (hcj : c≠j) :
      sharpCount (sharpStar (U.erase j) c)=2^(n-1)+2^(n-s) := by
    rw [sharpStarCount _ _ (Finset.mem_erase.mpr ⟨hcj,hc⟩),Finset.card_erase_of_mem hj,cardU]
    simp
  refine ⟨sharpPool U,sharpStar (U.erase r) c,sharpStar (U.erase l) c,
    fun S hS w => sharpPoolCovers (by omega : S.card<U.card) w,sharpPoolCard hc,?_,?_,?_,?_⟩
  · rw [ct r hr hcr,Nat.mul_add,Nat.mul_add,Nat.mul_one,←pow_add,←pow_add,←pow_add]
    have h1 : s+(n-1)=n+(s-1) := by omega
    have h2 : s+(n-s)=n := by omega
    rw [h1,h2]
  · rw [ct l hl hcl,ct r hr hcr]
  · intro w hw
    have hiff : sharpSat (sharpStar (U.erase r) c) w=true ↔ sharpSat (sharpStar (U.erase l) c) w=true := by
      rw [sharpStar_iff,sharpStar_iff,sharpErasePool U r hr w hw,sharpErasePool U l hl w hw]
    exact Bool.eq_iff_iff.mpr hiff
  · let w : SW n := fun k => decide (k=r)
    have hwa : sharpSat (sharpStar (U.erase r) c) w=true := by
      apply (sharpStar_iff _ _ _).2
      exact Or.inr (fun i hi => by simp [w,(Finset.mem_erase.mp hi).1])
    have hwb : sharpSat (sharpStar (U.erase l) c) w ≠ true := by
      intro h
      rcases (sharpStar_iff _ _ _).1 h with h | h
      · simpa [w,hcr] using h
      · have hbad := h r (Finset.mem_erase.mpr ⟨hrl,hr⟩)
        simpa [w] using hbad
    exact ⟨w,fun e => hwb (e ▸ hwa)⟩

end PEqualNP.Outside.L_lib_512

open PEqualNP.Outside.L_lib_512 in
theorem PEqualNP.Outside.L_lib_512 : (∀ (n s : ℕ), 3 ≤ s → s < n →
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let count := fun (G : F) => (Finset.univ.filter (fun u => sat G u = true)).card
  let covers := fun (P : Finset W) (r : ℕ) => ∀ S : Finset (Fin n), S.card ≤ r →
    ∀ pat : W, ∃ z ∈ P, ∀ bit ∈ S, z bit = pat bit
  let Q := 2 ^ n
  (∀ pool : Finset W, covers pool (s + 1) → ∀ A : F,
    let learned := fun x : W => ∀ T : Finset (Fin n), T.card ≤ 2 →
      ∃ y ∈ pool, sat A y = true ∧ ∀ j ∈ T, y j = x j
    (∀ x, learned x → sat A x = true) ∧
    (Q * (2 ^ (s - 1) + 1) ≤ 2 ^ s * count A →
      ∀ x, sat A x = true → learned x)) ∧
  (∃ (pool : Finset W) (A B : F), covers pool s ∧ 2 * pool.card = Q ∧
    2 ^ s * count A = Q * (2 ^ (s - 1) + 1) ∧ count B = count A ∧
    (∀ x ∈ pool, sat A x = sat B x) ∧ ∃ x, sat A x ≠ sat B x)) := by
  classical
  intro n s hs hn
  dsimp only
  constructor
  · intro P hp A
    refine ⟨learned_sat A P, ?_⟩
    intro density
    have hd : (2:ℕ)^n < 2 * count A := by
      have hpow : (2:ℕ)^s = 2^(s-1)*2 := by
        rw [←pow_succ, Nat.sub_add_cancel (show 1 ≤ s by omega)]
      have hlt : (2:ℕ)^n * 2^(s-1) < 2^n * (2^(s-1)+1) := by
        rw [Nat.mul_add, Nat.mul_one]
        have : 0 < (2:ℕ)^n := by positivity
        omega
      have hh := hlt.trans_le density
      change (2:ℕ)^n * 2^(s-1) < 2^s * count A at hh
      rw [hpow, Nat.mul_assoc, Nat.mul_comm (2^n)] at hh
      exact Nat.lt_of_mul_lt_mul_left hh
    apply recoveryFromObstruction hs A P hp hd (exists_accept_with_bit n A hd)
    · intro i b L f hi he x hx
      exact starRecovery hs hn P hp A i b L f hi he density x hx
    · intro D E H dE dH eH hD hE hH rD rE rH nc avoid
      exact clauseObstruction A D E H hD hE hH dE dH eH rD rE rH nc avoid
  · exact fridaySharp n s hs hn
