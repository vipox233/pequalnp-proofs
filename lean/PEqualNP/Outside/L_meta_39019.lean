import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39019

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276812992 * 2 ^ 32 + 4243127424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x1062bccc481b6634#64 ++ 0x21062bccc481b663#64 ++ 0xb0e7fccc483f6677#64 ++ 0xdb0e7fccc483f667#64 : BitVec 256),
   (0x0109805582c582d1#64 ++ 0x40109805582c582d#64 ++ 0x731980ff8fc787ff#64 ++ 0xb731980ff8fc787f#64 : BitVec 256),
   (0x0416050a9168a861#64 ++ 0x80416050a9168a86#64 ++ 0xfc1e0f0ff1f8f87f#64 ++ 0x7fc1e0f0ff1f8f87#64 : BitVec 256),
   (0x0ae00aa06c005506#64 ++ 0x00ae00aa06c00550#64 ++ 0xdfe00ff07e00ff8e#64 ++ 0xfdfe00ff07e00ff8#64 : BitVec 256),
   (0x2fbd50007fb60008#64 ++ 0x02fbd50007fb6000#64 ++ 0xaffff0007fff000d#64 ++ 0xfaffff0007fff000#64 : BitVec 256),
   (0x4fdfefff00000000#64 ++ 0x04fdfefff0000000#64 ++ 0x4fffffff80000003#64 ++ 0xf4fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [9, 5]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000804400010210 0x0000080440001021 0x300180cc08070677 0x9300180cc0807067

def z1 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x731980ff8fc787ff 0xb731980ff8fc787f

def z2 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xfc1e0f0ff1f8f87f 0x7fc1e0f0ff1f8f87

def z3 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xdfe00ff07e00ff8e 0xfdfe00ff07e00ff8

def z4 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0e7fccc483f6677 0xdb0e7fccc483f667

def z5 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xaffff0007fff000d 0xfaffff0007fff000

def z6 : W := mkw 0x4fdf6fbb00000000 0x04fdf6fbb0000000 0x4ffe7f3380000000 0x64ffe7f338000000

def z7 : W := mkw 0x451fe55f00000000 0x0451fe55f0000000 0x001ff00f80000001 0x0001ff00f8000000

def z8 : W := mkw 0x4fdfefff82c582d1 0x44fdfefff82c582d 0x7fffffff8fc787ff 0xf7fffffff8fc787f

def z9 : W := mkw 0x0000000082c582d1 0x40000000082c582d 0x300000000fc787fc 0x0300000000fc787f

def z10 : W := mkw 0x10201000481b6634 0x210201000481b663 0xb0000000483f6674 0x0b0000000483f667

def z11 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0x201e000f81f80071 0x0201e000f81f8007

def z12 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x03e000f00e000780 0x803e000f00e00078

def z13 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4fffffff80000003 0xf4fffffff8000000

def z14 : W := mkw 0x4fdfefff8048a861 0x84fdfefff8048a86 0x5fffffff8000f873 0xf5fffffff8000f87

def z15 : W := mkw 0x00400aa000005506 0x000400aa00000550 0x50000ff00000ff82 0x050000ff00000ff8

def z16 : W := mkw 0x251d500013b60008 0x0251d500013b6000 0x201ff00001ff0001 0x0201ff00001ff000

def z17 : W := mkw 0x4bc9eaf500000000 0x04bc9eaf50000000 0x03e1f0f000000000 0x803e1f0f00000000

def z18 : W := mkw 0x2f9d500013b60008 0x02f9d500013b6000 0x2ffff00001ff0001 0xf2ffff00001ff000

def z19 : W := mkw 0x7fffffff7fbf663c 0x27fffffff7fbf663 0xffffffffffff667f 0xfffffffffffff667

def z20 : W := mkw 0x0ac00aa000000000 0x00ac00aa00000000 0x03e000f000000000 0x803e000f00000000

def z21 : W := mkw 0x0ae20ea86c087526 0x00ae20ea86c08752 0xffe60ffc7e38ffff 0xfffe60ffc7e38fff

def z22 : W := mkw 0x1002b44c001b2230 0x21002b44c001b223 0x2007f00c003f0071 0x02007f00c003f007

def z23 : W := mkw 0x1060b8c448134614 0x21060b8c44813461 0x00e1f0c008070600 0x800e1f0c00807060

def z24 : W := mkw 0x102010006c1b7736 0x2102010006c1b773 0xb00000007e3ffffc 0x0b00000007e3ffff

def z25 : W := mkw 0x4f9d433300000000 0x04f9d43330000000 0x4f18033380000000 0x24f1803338000000

def z26 : W := mkw 0x251d500013b60008 0x0251d500013b6000 0x231ff0000fff000d 0xb231ff0000fff000

def z27 : W := mkw 0x00008055804182d1 0x400008055804182d 0x500000ff800087f2 0x0500000ff800087f

def z28 : W := mkw 0x2eb450007d320008 0x02eb450007d32000 0x8ce6700070380000 0x48ce670007038000

def z29 : W := mkw 0x0000804400010210 0x0000080440001021 0x100000cc00000672 0x0100000cc0000067

def z30 : W := mkw 0x455fefff00000000 0x0455fefff0000000 0x401fffff80000003 0x0401fffff8000000

def z31 : W := mkw 0x051f855f93edaaf1 0xc051f855f93edaaf 0x201f800f81ff0071 0x0201f800f81ff007

def z32 : W := mkw 0x20201000fff782d9 0x420201000fff782d 0xb00000007fff87fc 0x0b00000007fff87f

def z33 : W := mkw 0x0020904448130210 0x0002090444813021 0xb0e7f0cc483f0677 0xdb0e7f0cc483f067

def z34 : W := mkw 0x2fbdd055fff782d9 0x42fbdd055fff782d 0xfffff0ffffff87ff 0xffffff0ffffff87f

def z35 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xfce7ffcc783ffe7f 0xffce7ffcc783ffe7

def z36 : W := mkw 0x3ffffeec7fbf773e 0x23ffffeec7fbf773 0xfffffffc7fffffff 0xffffffffc7ffffff

def z37 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x3019800f8fc787fd 0x03019800f8fc787f

def z38 : W := mkw 0x0109000002840000 0x0010900000284000 0x231980000fc7000d 0xb231980000fc7000

def z39 : W := mkw 0x0f9d400000000000 0x00f9d40000000000 0x0ffff00000000001 0xf0ffff0000000000

def z40 : W := mkw 0x002000006c000000 0x0002000006c00000 0x800000007e00000c 0x0800000007e00000

def z41 : W := mkw 0x0000000002840000 0x0000000000284000 0x200000000fc7000c 0x0200000000fc7000

def z42 : W := mkw 0x251dd05593f782d9 0x4251dd05593f782d 0x201ff00f81ff0071 0x0201ff00f81ff007

def z43 : W := mkw 0x0109805500000000 0x0010980550000000 0x431980ff80000003 0xb431980ff8000000

def z44 : W := mkw 0x0020100048120000 0x0002010004812000 0xa0e7f000483f0005 0xda0e7f000483f000

def z45 : W := mkw 0x202010007fb60008 0x0202010007fb6000 0xa00000007fff000c 0x0a00000007fff000

def z46 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x2019800f81c70071 0x02019800f81c7007

def z47 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x8ce00f0070007800 0x48ce00f007000780

def z48 : W := mkw 0x0ac00aa000000000 0x00ac00aa00000000 0x5fe00ff00e00878e 0xf5fe00ff00e00878

def z49 : W := mkw 0x10209044481b6634 0x210209044481b663 0xb00180cc483f6677 0x9b00180cc483f667

def z50 : W := mkw 0x2436150afffea869 0x82436150afffea86 0xfc1e0f0ffffff87f 0x7fc1e0f0ffffff87

def z51 : W := mkw 0x0109001182c480c1 0x40109001182c480c 0x4318003387c08188 0x24318003387c0818

def z52 : W := mkw 0x10623c88481a6424 0x210623c88481a642 0x80e67c0040386000 0x480e67c004038600

def z53 : W := mkw 0x0414000011200000 0x0041400001120000 0xac1e000071f8000d 0x7ac1e000071f8000

def z54 : W := mkw 0x0002050a8048a861 0x80002050a8048a86 0x50000f0f8000f872 0x050000f0f8000f87

def z55 : W := mkw 0x2ba950006e960008 0x02ba950006e96000 0x03e1f0000e070000 0x803e1f0000e07000

def z56 : W := mkw 0x4fdfefff9168a861 0x84fdfefff9168a86 0xfffffffff1f8f87f 0xffffffffff1f8f87

def z57 : W := mkw 0x4fffefff6c005506 0x04fffefff6c00550 0xdffffffffe00ff8f 0xfdffffffffe00ff8

def z58 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0000ccc483f6676 0x0b0000ccc483f667

def z59 : W := mkw 0x0414010291608841 0x8041401029160884 0x7c18030fb1c0987f 0x37c18030fb1c0987

def z60 : W := mkw 0x0002050a8048a861 0x80002050a8048a86 0x0000000f80000070 0x00000000f8000007

def z61 : W := mkw 0x0002040800082020 0x0000204080008202 0xb0060c0c40386077 0x5b0060c0c4038607

def z62 : W := mkw 0x0416050a00082020 0x00416050a0008202 0xfc1e0f0fc0386077 0x7fc1e0f0fc038607

def z63 : W := mkw 0x0109805502850290 0x4010980550285029 0x030180f00e070780 0x8030180f00e07078

def z64 : W := mkw 0x1ae2beec6c1b7736 0x21ae2beec6c1b773 0xffe7fffc7e3fffff 0xfffe7fffc7e3ffff

def z65 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c0000007000000c 0x78c0000007000000

def z66 : W := mkw 0x0042accc00000000 0x00042accc0000000 0x00000ccc00000002 0x000000ccc0000000

def z67 : W := mkw 0x4042afff00000000 0x04042afff0000000 0x40000fff80000002 0x040000fff8000000

def z68 : W := mkw 0x6fffffff7fb60008 0x06fffffff7fb6000 0xefffffffffff000f 0xfefffffffffff000

def z69 : W := mkw 0x5062bfff481b6634 0x25062bfff481b663 0xf0e7ffffc83f6677 0xdf0e7ffffc83f667

def z70 : W := mkw 0x00221408481a2020 0x000221408481a202 0xb0e7fc0c483f6077 0xdb0e7fc0c483f607

def z71 : W := mkw 0x2fbf550afffea869 0x82fbf550afffea86 0xffffff0ffffff87f 0xfffffff0ffffff87

def z72 : W := mkw 0x4f9dc37700000000 0x04f9dc3770000000 0x4f1983ff80000003 0xb4f1983ff8000000

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc000f007000f80e 0x7dc000f007000f80

def z74 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0xdffffffff000f80f 0xfdffffffff000f80

def z75 : W := mkw 0x2ffd5aa07fb6550e 0x02ffd5aa07fb6550 0xfffffff07fffff8f 0xffffffff07fffff8

def z76 : W := mkw 0x0416050a11282820 0x80416050a1128282 0x0006000000380000 0x0000600000038000

def z77 : W := mkw 0x4e94432200000000 0x04e9443220000000 0x0c00030000000000 0x00c0003000000000

def z78 : W := mkw 0x0be98af5eec5d7d7 0x40be98af5eec5d7d 0xfff98fffffc7ffff 0xffff98fffffc7fff

def z79 : W := mkw 0x0109805502850290 0x4010980550285029 0x330180fc0e0707f7 0x9330180fc0e0707f

def z80 : W := mkw 0x5fffffff481b6634 0x25fffffff481b663 0xffffffffc83f6677 0xfffffffffc83f667

def z81 : W := mkw 0x0ae00aa0fd68fd67 0x80ae00aa0fd68fd6 0xffe00ff07ff8fffe 0xfffe00ff07ff8fff

def z82 : W := mkw 0x3ffffdceffffee7d 0xa3ffffdceffffee7 0xffffffcffffffe7f 0xfffffffcffffffe7

def z83 : W := mkw 0x2f9d400037a40008 0x02f9d400037a4000 0x2f1980003fc7000d 0xb2f1980003fc7000

def z84 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xdc060f0ff038f872 0x4dc060f0ff038f87

def z85 : W := mkw 0x2f9d400037a40008 0x02f9d400037a4000 0xaf1e000077f8000d 0x7af1e000077f8000

def z86 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0x10e1fccc08076672 0x810e1fccc0807667

def z87 : W := mkw 0x4fdfefff11200000 0x04fdfefff1120000 0xeffffffff1f8000f 0xfeffffffff1f8000

def z88 : W := mkw 0x6ffffffffffea869 0x86ffffffffffea86 0xfffffffffffff87f 0xffffffffffffff87

def z89 : W := mkw 0x4fdd4bb300000000 0x04fdd4bb30000000 0x4ff80ff380000002 0xf4ff80ff38000000

def z90 : W := mkw 0x1042accc00096634 0x21042accc0009663 0x10000ccc00006672 0x010000ccc0000667

def z91 : W := mkw 0x3ffffccc7fbf663c 0x23ffffccc7fbf663 0xbffffccc7fff667f 0xfbffffccc7fff667

def z92 : W := mkw 0x2fbdd0557fb70298 0x42fbdd0557fb7029 0xaffff0f07fff078d 0xfaffff0f07fff078

def z93 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x531800ff87c087fa 0x2531800ff87c087f

def z94 : W := mkw 0x6fbd53337fb60008 0x06fbd53337fb6000 0xeffff333ffff000d 0xfeffff333ffff000

def z95 : W := mkw 0x2ba950006e960008 0x02ba950006e96000 0x23f9f0000fc7000d 0xb23f9f0000fc7000

def z96 : W := mkw 0x4ed66faa00000000 0x04ed66faa0000000 0x0ce67f0000000000 0x40ce67f000000000

def z97 : W := mkw 0x0f9f450a00000000 0x00f9f450a0000000 0x4fffff0f80000003 0xf4fffff0f8000000

def z98 : W := mkw 0x4fdfefff82c582d1 0x44fdfefff82c582d 0x6fffffff81c70073 0xf6fffffff81c7007

def z99 : W := mkw 0x14763d8ad97aec65 0xa14763d8ad97aec6 0xfcfe7f0ff1f8f87f 0x7fcfe7f0ff1f8f87

def z100 : W := mkw 0x0109000082c48041 0x00109000082c4804 0x7319800f8fc7807f 0xb7319800f8fc7807

def z101 : W := mkw 0x202010007fb60008 0x0202010007fb6000 0xa0e7f0007fff000d 0xda0e7f0007fff000

def z102 : W := mkw 0x0000000080408041 0x0000000008040804 0x7018000f81c0807f 0x37018000f81c0807

def z103 : W := mkw 0x051f855f93edaaf1 0xc051f855f93edaaf 0xff1f8fffffffffff 0xfff1f8ffffffffff

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0xdf000ff07e00ff8e 0xfdf000ff07e00ff8

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x530000f00e00878e 0xb530000f00e00878

def z106 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xf3e7fcfc4e3fe7ff 0xff3e7fcfc4e3fe7f

def z107 : W := mkw 0x000000009168a861 0x8000000009168a86 0xb000000071f8f87c 0x0b000000071f8f87

def z108 : W := mkw 0x04760d8ad968ec65 0x804760d8ad968ec6 0xfcfe0fcff9f8fe7f 0xffcfe0fcff9f8fe7

def z109 : W := mkw 0x0ac2aeec00000000 0x00ac2aeec0000000 0x4fe7fffc00000003 0xf4fe7fffc0000000

def z110 : W := mkw 0x0042accc00000000 0x00042accc0000000 0x00e7fccc00000003 0xd00e7fccc0000000

def z111 : W := mkw 0x0fbd500048120000 0x00fbd50004812000 0xaffff000483f0005 0xfaffff000483f000

def z112 : W := mkw 0x0000000080408041 0x0000000008040804 0x2018000f81c00071 0x02018000f81c0007

def z113 : W := mkw 0x014bacdd00000000 0x0014bacdd0000000 0x43fffcff80000003 0xf43fffcff8000000

def z114 : W := mkw 0x116bbcddcadfe6f5 0x6116bbcddcadfe6f 0xf3fffcffcfffe7ff 0xff3fffcffcfffe7f

def z115 : W := mkw 0x1042adce8049ee75 0xa1042adce8049ee7 0x50000fcf8000fe72 0x050000fcf8000fe7

def z116 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x701980ff81c787f3 0x0701980ff81c787f

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x00e7f00000000001 0xd00e7f0000000000

def z118 : W := mkw 0x041400009168a861 0x8041400009168a86 0xbc1e000071f8f87d 0x7bc1e000071f8f87

def z119 : W := mkw 0x4fffefffeec5d7d7 0x44fffefffeec5d7d 0xffffffffffc7ffff 0xfffffffffffc7fff

def z120 : W := mkw 0x110bb45d82dfa2f1 0x6110bb45d82dfa2f 0x731ff0ff8fff87ff 0xb731ff0ff8fff87f

def z121 : W := mkw 0x0060088048004404 0x0006008804800440 0x90e00cc048006606 0xd90e00cc04800660

def z122 : W := mkw 0x2000100013b60008 0x02000100013b6000 0x2000000001ff0000 0x02000000001ff000

def z123 : W := mkw 0x0fbd40006c000000 0x00fbd40006c00000 0x8ffff0007e00000d 0xf8ffff0007e00000

def z124 : W := mkw 0x10023408001a2020 0x210023408001a202 0x0006700000380000 0x0000670000038000

def z125 : W := mkw 0x5ef6ffee481b6634 0x25ef6ffee481b663 0xbce7ffcc483f6677 0xdbce7ffcc483f667

def z126 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xcc1e0f03f1f8f808 0x6cc1e0f03f1f8f80

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c00030030009808 0x24c0003003000980

def z128 : W := mkw 0x0414010291608841 0x8041401029160884 0x4c180303b1c09808 0x24c180303b1c0980

def z129 : W := mkw 0x21299055fff782d9 0x421299055fff782d 0xf31980ffffff87ff 0xbf31980ffffff87f

def z130 : W := mkw 0x157fbddfdbffeef5 0xe157fbddfdbffeef 0xffffffffffffffff 0xffffffffffffffff

def z131 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x0cffff0f80000001 0x40cffff0f8000000

def z132 : W := mkw 0x4fdfefff02840000 0x04fdfefff0284000 0x6fffffff8fc7000f 0xf6fffffff8fc7000

def z133 : W := mkw 0x5fffffff48134614 0x25fffffff4813461 0x4fffffff88070603 0xf4fffffff8807060

def z134 : W := mkw 0x0416050a00000000 0x00416050a0000000 0x4c1e0f0f80000003 0x74c1e0f0f8000000

def z135 : W := mkw 0x0ba98055eec582d1 0x40ba98055eec582d 0xfff980ffffc787ff 0xffff980ffffc787f

def z136 : W := mkw 0x0ac00aa000000000 0x00ac00aa00000000 0x4fe00ff000000002 0xf4fe00ff00000000

def z137 : W := mkw 0x6fdfefff37a40008 0x06fdfefff37a4000 0x4fffffffb7c0000b 0xf4fffffffb7c0000

def z138 : W := mkw 0x0000000082c582d1 0x40000000082c582d 0x2000000001c70070 0x02000000001c7007

def z139 : W := mkw 0x051f051b93eca8e1 0xc051f051b93eca8e 0xff1e0f3ff7f8f9ff 0x7ff1e0f3ff7f8f9f

def z140 : W := mkw 0x451fe55f9168a861 0x8451fe55f9168a86 0x201ff00f81f80071 0x0201ff00f81f8007

def z141 : W := mkw 0x4fdfefff24001102 0x04fdfefff2400110 0x4fffffffb600998b 0xf4fffffffb600998

def z142 : W := mkw 0x0aa000006c000000 0x00aa000006c00000 0x8fe000007e00000c 0xf8fe000007e00000

def z143 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0x6c1e0f0f81f80073 0x76c1e0f0f81f8007

def z144 : W := mkw 0x0ac00aa024005506 0x00ac00aa02400550 0x5f000ff03600ff8a 0x25f000ff03600ff8

def z145 : W := mkw 0x0ae00aa0ec40d547 0x00ae00aa0ec40d54 0xfff80fffffc0ffff 0xffff80fffffc0fff

def z146 : W := mkw 0x051d805593e582d1 0x4051d805593e582d 0xff1f80ffffff87ff 0xfff1f80ffffff87f

def z147 : W := mkw 0x451fe55f9168a861 0x8451fe55f9168a86 0xfc1fff0ff1f8f87f 0x7fc1fff0ff1f8f87

def z148 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xaf1800007fff000c 0x2af1800007fff000

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x90000c0040006006 0x590000c004000600

def z150 : W := mkw 0x2f9d400037a40008 0x02f9d400037a4000 0x0f18000037c00008 0x20f18000037c0000

def z151 : W := mkw 0x4fdfefff00005506 0x04fdfefff0000550 0x5fffffff8000ff83 0xf5fffffff8000ff8

def z152 : W := mkw 0x1042bccc001b2230 0x21042bccc001b223 0x20e7fccc003f0073 0xd20e7fccc003f007

def z153 : W := mkw 0x0062bccc48120000 0x00062bccc4812000 0xa0e7fccc483f0007 0xda0e7fccc483f000

def z154 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x4fe003f03e009f88 0xa4fe003f03e009f8

def z155 : W := mkw 0x0414000011200000 0x0041400001120000 0xfc1e0f0071f8f80f 0x7fc1e0f0071f8f80

def z156 : W := mkw 0x0109805500000000 0x0010980550000000 0x030180f000000000 0x8030180f00000000

def z157 : W := mkw 0x0416050a11282820 0x80416050a1128282 0x8c060f0070387800 0x48c060f007038780

def z158 : W := mkw 0x0a80022024001102 0x00a8002202400110 0x5f0003f03e009f8e 0xb5f0003f03e009f8

def z159 : W := mkw 0x2fbd5000fff782d9 0x42fbd5000fff782d 0xbffff0007fff87fd 0xfbffff0007fff87f

def z160 : W := mkw 0x0414010291608841 0x8041401029160884 0x0018000381c00000 0x00018000381c0000

def z161 : W := mkw 0x455feddf00000000 0x0455feddf0000000 0x00fffccf80000003 0xd00fffccf8000000

def z162 : W := mkw 0x002000006c005506 0x0002000006c00550 0x900000007e00ff8c 0x0900000007e00ff8

def z163 : W := mkw 0x1062bccc6c1b7736 0x21062bccc6c1b773 0xb0e7fccc7e3fffff 0xdb0e7fccc7e3ffff

def z164 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x0fe7fff000000000 0xc0fe7fff00000000

def z165 : W := mkw 0x4fdfefff804182d1 0x44fdfefff804182d 0x5fffffff800087f3 0xf5fffffff800087f

def z166 : W := mkw 0x2ffd5aa07fb6550e 0x02ffd5aa07fb6550 0xaffff0f07fff078d 0xfaffff0f07fff078

def z167 : W := mkw 0x2b89400026840008 0x02b8940002684000 0x0300000006000000 0x0030000000600000

def z168 : W := mkw 0x4ef66faa6c005506 0x04ef66faa6c00550 0xdfe67ff07e00ff8e 0xfdfe67ff07e00ff8

def z169 : W := mkw 0x1ef6bfeefd7bff77 0xa1ef6bfeefd7bff7 0xffffffffffffffff 0xffffffffffffffff

def z170 : W := mkw 0x0aa000006c000000 0x00aa000006c00000 0xdfe00f007e00f80e 0xfdfe00f007e00f80

def z171 : W := mkw 0x253d50005bb60008 0x0253d50005bb6000 0xa0fff00049ff0005 0xda0fff00049ff000

def z172 : W := mkw 0x2ffffccc7fb60008 0x02ffffccc7fb6000 0xaffffccc7fff000f 0xfaffffccc7fff000

def z173 : W := mkw 0x4ed6efff00000000 0x04ed6efff0000000 0x4ce67fff80000002 0x44ce67fff8000000

def z174 : W := mkw 0x0000022000001102 0x0000002200000110 0x4000033000009980 0x0400003300000998

def z175 : W := mkw 0x4ef66faa6c005506 0x04ef66faa6c00550 0x8ce67f0070007800 0x48ce67f007000780

def z176 : W := mkw 0x0ae08af5ec41d7d7 0x40ae08af5ec41d7d 0xdfe00ffffe00fffe 0xfdfe00ffffe00fff

def z177 : W := mkw 0x10221408481b6634 0x210221408481b663 0xb0060c0c483f6677 0x5b0060c0c483f667

def z178 : W := mkw 0x4fdfefff91608841 0x84fdfefff9160884 0x4fffffffb1c0980b 0xf4fffffffb1c0980

def z179 : W := mkw 0x0000804482c582d1 0x40000804482c582d 0x300180cc0fc787ff 0x9300180cc0fc787f

def z180 : W := mkw 0x0109000002840000 0x0010900000284000 0x731980f00fc7878f 0xb731980f00fc7878

def z181 : W := mkw 0x0000000080408041 0x0000000008040804 0x731800ff8fc087ff 0xb731800ff8fc087f

def z182 : W := mkw 0x2f9d4102b7e48849 0x82f9d4102b7e4884 0x4f180303b7c09808 0x24f180303b7c0980

def z183 : W := mkw 0x1ae2beec481b6634 0x21ae2beec481b663 0xffe7fffc483f6677 0xfffe7fffc483f667

def z184 : W := mkw 0x0416050a8048a861 0x80416050a8048a86 0x5c1e0f0f8000f873 0x75c1e0f0f8000f87

def z185 : W := mkw 0x4fffefff6c005506 0x04fffefff6c00550 0xcffffffff0007803 0xfcffffffff000780

def z186 : W := mkw 0x1476bdced97bee75 0xa1476bdced97bee7 0xfcffffcff9fffe7f 0xffcffffcff9fffe7

def z187 : W := mkw 0x0000805500000000 0x0000080550000000 0x400000ff80000002 0x0400000ff8000000

def z188 : W := mkw 0x0434100059320000 0x0043410005932000 0xacfff00079ff000d 0xfacfff00079ff000

def z189 : W := mkw 0x0109000082c582d1 0x40109000082c582d 0x331980000fc787fd 0xb331980000fc787f

def z190 : W := mkw 0x0042accc00010210 0x00042accc0001021 0x30e7fccc08070677 0xd30e7fccc0807067

def z191 : W := mkw 0x4bcbefff00000000 0x04bcbefff0000000 0x43e1ffff80000002 0x843e1ffff8000000

def z192 : W := mkw 0x5042afff00096634 0x25042afff0009663 0x50000fff80006672 0x050000fff8000667

def z193 : W := mkw 0x1002b44c001b2230 0x21002b44c001b223 0xb007fc0c403f6077 0x5b007fc0c403f607

def z194 : W := mkw 0x0020100048120000 0x0002010004812000 0x00e1f00008070000 0x800e1f0000807000

def z195 : W := mkw 0x1062bdcec85bee75 0xa1062bdcec85bee7 0xf0e7ffcfc83ffe77 0xdf0e7ffcfc83ffe7

def z196 : W := mkw 0x0109805502850290 0x4010980550285029 0x0001800000070000 0x0000180000007000

def z197 : W := mkw 0x2aa010007fb60008 0x02aa010007fb6000 0xafe000007fff000c 0xfafe000007fff000

def z198 : W := mkw 0x0ae00aa06c000000 0x00ae00aa06c00000 0xcfe00ff07e00000e 0xfcfe00ff07e00000

def z199 : W := mkw 0x0fff8fffffedfff7 0xc0fff8fffffedfff 0xffff8fffffffffff 0xfffff8ffffffffff

def z200 : W := mkw 0x00008055804182d1 0x400008055804182d 0x0000000f80000070 0x00000000f8000007

def z201 : W := mkw 0x012910004a960000 0x0012910004a96000 0xa3fff0004fff000d 0xfa3fff0004fff000

def z202 : W := mkw 0x0000000082c582d1 0x40000000082c582d 0x730000f00fc787fe 0xb730000f00fc787f

def z203 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xff1e0ffffff8ffff 0xfff1e0ffffff8fff

def z204 : W := mkw 0x0109001100000000 0x0010900110000000 0x4318003380000000 0x2431800338000000

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000f000000f802 0x050000f000000f80

def z206 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x5fffffff8e00878f 0xf5fffffff8e00878

def z207 : W := mkw 0x051d011393e488c1 0xc051d011393e488c 0x4f180333b7c09988 0x24f180333b7c0998

def z208 : W := mkw 0x4fdfefff9168a861 0x84fdfefff9168a86 0x6fffffff81f80073 0xf6fffffff81f8007

def z209 : W := mkw 0x2ef45aa07d32550e 0x02ef45aa07d32550 0x8ce67f0070387800 0x48ce67f007038780

def z210 : W := mkw 0x10201000481b6634 0x210201000481b663 0xb0e7f000483f6675 0xdb0e7f000483f667

def z211 : W := mkw 0x1476bdce481b6634 0x21476bdce481b663 0xfcffffcfc83f6677 0xffcffffcfc83f667

def z212 : W := mkw 0x0109805593edaaf1 0xc0109805593edaaf 0xf31980ffffffffff 0xbf31980fffffffff

def z213 : W := mkw 0x0000000082c582d1 0x40000000082c582d 0x7018000f8fc787ff 0x37018000f8fc787f

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x500000000000800e 0x3500000000000800

def z215 : W := mkw 0x1060b8c448134614 0x21060b8c44813461 0x30e1f0cc08070677 0x930e1f0cc0807067

def z216 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xac1e0f0ff1f87871 0x4ac1e0f0ff1f8787

def z217 : W := mkw 0x4fdf6faa00000000 0x04fdf6faa0000000 0x0fffff0000000001 0xf0fffff000000000

def z218 : W := mkw 0x4fffeffffd68fd67 0x84fffeffffd68fd6 0xfffffffffff8ffff 0xffffffffffff8fff

def z219 : W := mkw 0x2be95aa06e96550e 0x02be95aa06e96550 0xdfe1fff07e07ff8e 0xfdfe1fff07e07ff8

def z220 : W := mkw 0x0414010211200800 0x8041401021120080 0x0c00030030001800 0x00c0003003000180

def z221 : W := mkw 0x0414010200000000 0x0041401020000000 0x4c18030380000000 0x24c1803038000000

def z222 : W := mkw 0x041401029168a861 0x8041401029168a86 0xfc180303f1f8f87c 0x2fc180303f1f8f87

def z223 : W := mkw 0x6ffffffffff782d9 0x46ffffffffff782d 0xffffffffffff87ff 0xfffffffffffff87f

def z224 : W := mkw 0x202010007fb6550e 0x0202010007fb6550 0xb00000007fffff8c 0x0b00000007fffff8

def z225 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xa0e7fc0c403f6071 0x4a0e7fc0c403f607

def z226 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xacfff00071ff0001 0x4acfff00071ff000

def z227 : W := mkw 0x4fdfefff00082020 0x04fdfefff0008202 0xffffffffc0386077 0xfffffffffc038607

def z228 : W := mkw 0x1040a8c400014614 0x21040a8c40001461 0x000000c000000600 0x0000000c00000060

def z229 : W := mkw 0x0109805500000000 0x0010980550000000 0x531980ff8e00878f 0xb531980ff8e00878

def z230 : W := mkw 0x2fbdd0447fb70218 0x02fbdd0447fb7021 0xbffff0cc7fff067f 0xfbffff0cc7fff067

def z231 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0x20e7f0cc083f0671 0x820e7f0cc083f067

def z232 : W := mkw 0x0a80000000000000 0x00a8000000000000 0x0fe0000000000000 0xf0fe000000000000

def z233 : W := mkw 0x4f9d433300000000 0x04f9d43330000000 0x4ffff33380000001 0xf4ffff3338000000

def z234 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x03fff0ff80000001 0x803fff0ff8000000

def z235 : W := mkw 0x002000006c005506 0x0002000006c00550 0x000000000e000780 0x0000000000e00078

def z236 : W := mkw 0x651ff55f13b60008 0x0651ff55f13b6000 0x201ff00f81ff0001 0x0201ff00f81ff000

def z237 : W := mkw 0x10623c88481a6424 0x210623c88481a642 0x90e67cc048386606 0xd90e67cc04838660

def z238 : W := mkw 0x0aa000006c000000 0x00aa000006c00000 0x8ce0000070000000 0x48ce000007000000

def z239 : W := mkw 0x1062bcccc85be675 0x21062bcccc85be67 0xf0fffccfc9ffe67f 0xff0fffccfc9ffe67

def z240 : W := mkw 0x0414000011200000 0x0041400001120000 0x8c06000070380000 0x48c0600007038000

def z241 : W := mkw 0x002000006c005506 0x0002000006c00550 0x8000000070007800 0x0800000007000780

def z242 : W := mkw 0x0ef60faafd68fd67 0x80ef60faafd68fd6 0xfffe0ffffff8ffff 0xffffe0ffffff8fff

def z243 : W := mkw 0x4fffefff48004404 0x04fffefff4800440 0xdfffffffc8006607 0xfdfffffffc800660

def z244 : W := mkw 0x251f550a93fea869 0x8251f550a93fea86 0xfc1fff0ff1fff87f 0x7fc1fff0ff1fff87

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x030000000e00000c 0xb030000000e00000

def z246 : W := mkw 0x4f9d433382c480c1 0x44f9d433382c480c 0x4f18033387c08188 0x24f18033387c0818

def z247 : W := mkw 0x0ae00aa0eec5d7d7 0x40ae00aa0eec5d7d 0xffe00ff07fc7fffe 0xfffe00ff07fc7fff

def z248 : W := mkw 0x0109805502850290 0x4010980550285029 0x530180f00e07878e 0xb530180f00e07878

def z249 : W := mkw 0x0416050a00000000 0x00416050a0000000 0x001e000f80000001 0x0001e000f8000000

def z250 : W := mkw 0x00008055804182d1 0x400008055804182d 0x530000ff8e0087fe 0xb530000ff8e0087f

def z251 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xb01e000ff1f8f87d 0x0b01e000ff1f8f87

def z252 : W := mkw 0x0000805500010290 0x4000080550001029 0x000000f000000780 0x0000000f00000078

def z253 : W := mkw 0x2f9d500037b60008 0x02f9d500037b6000 0x2f1ff00037ff0009 0x22f1ff00037ff000

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c000f0070007800 0x48c000f007000780

def z255 : W := mkw 0x2ffddaf5fff7d7df 0x42ffddaf5fff7d7d 0xffffffffffffffff 0xffffffffffffffff

def z256 : W := mkw 0x0be98af5eec5d7d7 0x40be98af5eec5d7d 0x73f980ff8fc787ff 0xb73f980ff8fc787f

def z257 : W := mkw 0x0ac00aa024001102 0x00ac00aa02400110 0x4fe00ff03600998a 0xf4fe00ff03600998

def z258 : W := mkw 0x0000000000000000 0x0000000000000000 0x2001800008070005 0x9200180000807000

def z259 : W := mkw 0x253d50007fb60008 0x0253d50007fb6000 0xa01ff0007fff000d 0x0a01ff0007fff000

def z260 : W := mkw 0x5fdfefff00096634 0x25fdfefff0009663 0x5fffffff80006673 0xf5fffffff8000667

def z261 : W := mkw 0x00008055804182d1 0x400008055804182d 0x700180ff880787f7 0x9700180ff880787f

def z262 : W := mkw 0x0ae08ae46c015716 0x00ae08ae46c01571 0xffe18ffc7e07ffff 0xfffe18ffc7e07fff

def z263 : W := mkw 0x1ae23ea86c1a7526 0x21ae23ea86c1a752 0xdfe67ff07e38ff8e 0xfdfe67ff07e38ff8

def z264 : W := mkw 0x1042accc00096634 0x21042accc0009663 0xb0060ccc40386677 0x5b0060ccc4038667

def z265 : W := mkw 0x4be9eaf56c005506 0x04be9eaf56c00550 0xdfe1fff07e00ff8e 0xfdfe1fff07e00ff8

def z266 : W := mkw 0x0416050a11282820 0x80416050a1128282 0xcc1e0f0ff0387803 0x7cc1e0f0ff038780

def z267 : W := mkw 0x0002040800082020 0x0000204080008202 0xfc060f0c7038f87f 0x7fc060f0c7038f87

def z268 : W := mkw 0x1062beec481b7736 0x21062beec481b773 0xf0e7fffc483ffff7 0xdf0e7fffc483ffff

def z269 : W := mkw 0x4bc9eaf502850290 0x44bc9eaf50285029 0x03e1f0f00e070780 0x803e1f0f00e07078

def z270 : W := mkw 0x2fbf550a7fb60008 0x02fbf550a7fb6000 0xefffff0fffff000f 0xfefffff0fffff000

def z271 : W := mkw 0x0060188048124404 0x0006018804812440 0xb0e7fcc0483f6607 0xdb0e7fcc0483f660

def z272 : W := mkw 0x2fbf550a7fbe2828 0x82fbf550a7fbe282 0xafffff007fff780d 0xfafffff007fff780

def z273 : W := mkw 0x2ffd58807fb6440c 0x02ffd58807fb6440 0xbffffcc07fff660f 0xfbffffcc07fff660

def z274 : W := mkw 0x0000000011282820 0x8000000001128282 0x8000000070387800 0x0800000007038780

def z275 : W := mkw 0x10201000cadfe6f5 0x610201000cadfe6f 0xb00000004fffe7fc 0x0b00000004fffe7f

def z276 : W := mkw 0x6fffffff7d320008 0x06fffffff7d32000 0xcffffffff0380003 0xfcffffffff038000

def z277 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xffffff007ffff80f 0xfffffff007ffff80

def z278 : W := mkw 0x0060088048004404 0x0006008804800440 0x00e000c008000600 0x800e000c00800060

def z279 : W := mkw 0x4042afff8048a861 0x84042afff8048a86 0x50000fff8000f872 0x050000fff8000f87

def z280 : W := mkw 0x0062accc48004404 0x00062accc4800440 0x90e7fccc48006607 0xd90e7fccc4800660

def z281 : W := mkw 0x1042aeec00097736 0x21042aeec0009773 0x50000ffc0000fff2 0x050000ffc0000fff

def z282 : W := mkw 0x2414500011320008 0x0241450001132000 0x0006700000380000 0x0000670000038000

def z283 : W := mkw 0x414bafff00000000 0x0414bafff0000000 0x43198fff80000003 0xb43198fff8000000

def z284 : W := mkw 0x5bebfefd481b6634 0x25bebfefd481b663 0xb3e7fcfc483f6677 0xdb3e7fcfc483f667

def z285 : W := mkw 0x451d411300000000 0x0451d41130000000 0x0018000380000000 0x0001800038000000

def z286 : W := mkw 0x0a80022024001102 0x00a8002202400110 0x4f00033036009988 0x24f0003303600998

def z287 : W := mkw 0x1ae01aa06c1b7736 0x21ae01aa06c1b773 0xffe00ff07e3ffffe 0xfffe00ff07e3ffff

def z288 : W := mkw 0x0414000091608041 0x0041400009160804 0xfc1e000ff1f8807f 0x7fc1e000ff1f8807

def z289 : W := mkw 0x00200000fd68fd67 0x800200000fd68fd6 0xb00000007ff8fffc 0x0b00000007ff8fff

def z290 : W := mkw 0x2ae01aa07fb6550e 0x02ae01aa07fb6550 0xffe00ff07fffff8e 0xfffe00ff07fffff8

def z291 : W := mkw 0x40422faa00000000 0x040422faa0000000 0x00000f0000000000 0x000000f000000000

def z292 : W := mkw 0x2fbf550afffea869 0x82fbf550afffea86 0xaffff00fffff007d 0xfaffff00fffff007

def z293 : W := mkw 0x1062bccc48134614 0x21062bccc4813461 0x00e7fccc08070603 0xd00e7fccc0807060

def z294 : W := mkw 0x0b898275a6c593d3 0x40b898275a6c593d 0x7f1983ffbfc79fff 0xb7f1983ffbfc79ff

def z295 : W := mkw 0x006008806c005506 0x0006008806c00550 0x90e00cc07e00ff8e 0xd90e00cc07e00ff8

def z296 : W := mkw 0x2eb450007d320008 0x02eb450007d32000 0xacfe700071f8000d 0x7acfe700071f8000

def z297 : W := mkw 0x10422c8800086424 0x210422c880008642 0x00000c0000006000 0x000000c000000600

def z298 : W := mkw 0x002000006c005506 0x0002000006c00550 0xd30000f07e00ff8e 0xbd30000f07e00ff8

def z299 : W := mkw 0x014bacdd82c582d1 0x4014bacdd82c582d 0x73fffcff8fc787ff 0xf73fffcff8fc787f

def z300 : W := mkw 0x1042accc00096634 0x21042accc0009663 0x10e7fccc00006673 0xd10e7fccc0000667

def z301 : W := mkw 0x0109000002840000 0x0010900000284000 0x0318000007c00008 0x20318000007c0000

def z302 : W := mkw 0x01098055804182d1 0x401098055804182d 0x531980ff800087f3 0xb531980ff800087f

def z303 : W := mkw 0x1062bccc481a6424 0x21062bccc481a642 0x80e7fccc40386003 0xd80e7fccc4038600

def z304 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x231980ff8fc707f1 0x8231980ff8fc707f

def z305 : W := mkw 0x000000008048a861 0x8000000008048a86 0x100000000000f870 0x0100000000000f87

def z306 : W := mkw 0x0000000000000000 0x0000000000000000 0x430000f000000002 0xb430000f00000000

def z307 : W := mkw 0x1ae0bae46c135716 0x21ae0bae46c13571 0xdfe1fff07e07ff8e 0xfdfe1fff07e07ff8

def z308 : W := mkw 0x0002040800082020 0x0000204080008202 0x80060c0040386000 0x480060c004038600

def z309 : W := mkw 0x0109000002840000 0x0010900000284000 0x2019800001c70001 0x02019800001c7000

def z310 : W := mkw 0x3bebfccc6e9f663c 0x23bebfccc6e9f663 0xb3e7fccc4e3f6677 0xdb3e7fccc4e3f667

def z311 : W := mkw 0x0002050a8048a861 0x80002050a8048a86 0xdc000f0ff000f87e 0x7dc000f0ff000f87

def z312 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xdce00ff07000ff82 0x4dce00ff07000ff8

def z313 : W := mkw 0x1062bccccadfe6f5 0x61062bccccadfe6f 0xb0e7fccc4fffe7ff 0xdb0e7fccc4fffe7f

def z314 : W := mkw 0x0414000000000000 0x0041400000000000 0x0c1e000000000001 0x70c1e00000000000

def z315 : W := mkw 0x0109001182c480c1 0x40109001182c480c 0x631980338fc7818d 0xb631980338fc7818

def z316 : W := mkw 0x4ae2afff6c005506 0x04ae2afff6c00550 0xdfe00ffffe00ff8e 0xfdfe00ffffe00ff8

def z317 : W := mkw 0x4fdfefff11282820 0x84fdfefff1128282 0xcffffffff0387803 0xfcffffffff038780

def z318 : W := mkw 0x2f9d4011b7e480c9 0x42f9d4011b7e480c 0x4f180033b7c08188 0x24f180033b7c0818

def z319 : W := mkw 0x4fddebf700000000 0x04fddebf70000000 0x4ff9f3f380000000 0xa4ff9f3f38000000

def z320 : W := mkw 0x4bc9eaf582c582d1 0x44bc9eaf582c582d 0x73f9f0ff8fc787ff 0xb73f9f0ff8fc787f

def z321 : W := mkw 0x0000000000082020 0x0000000000008202 0xb000000040386074 0x0b00000004038607

def z322 : W := mkw 0x1020100048134614 0x2102010004813461 0x0000000008070600 0x0000000000807060

def z323 : W := mkw 0x1ffffccc481b6634 0x21ffffccc481b663 0xbffffccc483f6677 0xfbffffccc483f667

def z324 : W := mkw 0x5fdfffff001b2230 0x25fdfffff001b223 0x6fffffff803f0073 0xf6fffffff803f007

def z325 : W := mkw 0x4fffefff6c000000 0x04fffefff6c00000 0xcffffffffe00000f 0xfcffffffffe00000

def z326 : W := mkw 0x10201000481a6424 0x210201000481a642 0x8000000040386000 0x0800000004038600

def z327 : W := mkw 0x116bbcdd481b6634 0x2116bbcdd481b663 0xf3fffcffc83f6677 0xff3fffcffc83f667

def z328 : W := mkw 0x6fff7faa7fb60008 0x06fff7faa7fb6000 0xafffff007fff000d 0xfafffff007fff000

def z329 : W := mkw 0x4ed66faa11282820 0x84ed66faa1128282 0x8ce67f0070387800 0x48ce67f007038780

def z330 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0x90e67ccc40386672 0x490e67ccc4038667

def z331 : W := mkw 0x5fffffff6c1b7736 0x25fffffff6c1b773 0xfffffffffe3fffff 0xffffffffffe3ffff

def z332 : W := mkw 0x1416b54e917baa71 0xa1416b54e917baa7 0xfc1fff0ff1fff87f 0x7fc1fff0ff1fff87

def z333 : W := mkw 0x0416040811282020 0x0041604081128202 0xbc1e0c0c71f8607f 0x7bc1e0c0c71f8607

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000000e00878c 0x0100000000e00878

def z335 : W := mkw 0x2fbd5011fff680c9 0x42fbd5011fff680c 0xeffff033ffff818d 0xfeffff033ffff818

def z336 : W := mkw 0x0416855f9169aaf1 0xc0416855f9169aaf 0xfc1e0ffff1f8ffff 0x7fc1e0ffff1f8fff

def z337 : W := mkw 0x0040a8c400000000 0x00040a8c40000000 0x00e1f0c000000000 0x800e1f0c00000000

def z338 : W := mkw 0x0000000080408041 0x0000000008040804 0x5000000f80008072 0x05000000f8000807

def z339 : W := mkw 0x4bc9eaf500000000 0x04bc9eaf50000000 0x43f9f0ff80000003 0xb43f9f0ff8000000

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x4300003006008188 0x2430000300600818

def z341 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xdce00f007000f80e 0x7dce00f007000f80

def z342 : W := mkw 0x0000000000000000 0x0000000000000000 0x900000007000f80c 0x0900000007000f80

def z343 : W := mkw 0x1000b04400130210 0x21000b0440013021 0x0001f00000070000 0x00001f0000007000

def z344 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0x5c180f0fb1c0f87a 0x25c180f0fb1c0f87

def z345 : W := mkw 0x4bc9eaf500000000 0x04bc9eaf50000000 0x4fe1fff000000002 0xf4fe1fff00000000

def z346 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x93e00cf04e006786 0xd93e00cf04e00678

def z347 : W := mkw 0x0000000080408041 0x0000000008040804 0xfc180f0ff1c0f87f 0x7fc180f0ff1c0f87

def z348 : W := mkw 0x2eb450007d320008 0x02eb450007d32000 0x8fe670007e38000c 0xf8fe670007e38000

def z349 : W := mkw 0x2fbd52207fb6110a 0x02fbd52207fb6110 0xeffff3307fff998d 0xfeffff3307fff998

def z350 : W := mkw 0x1022b44c481b2230 0x21022b44c481b223 0xa0e7f00c483f0075 0xda0e7f00c483f007

def z351 : W := mkw 0x5fffffffd97bee75 0xa5fffffffd97bee7 0xfffffffff9fffe7f 0xffffffffff9fffe7

def z352 : W := mkw 0x0109001182c480c1 0x40109001182c480c 0x531800f38fc0878e 0xb531800f38fc0878

def z353 : W := mkw 0x051f050a93eca861 0x8051f050a93eca86 0xff1f8f0ffffff87f 0xfff1f8f0ffffff87

def z354 : W := mkw 0x0ef60faa7d287d26 0x80ef60faa7d287d2 0x8ce60f0070387800 0x48ce60f007038780

def z355 : W := mkw 0x20201000fffea869 0x820201000fffea86 0xb00000007ffff87c 0x0b00000007ffff87

def z356 : W := mkw 0x251d400013a40008 0x0251d400013a4000 0x0018000001c00000 0x00018000001c0000

def z357 : W := mkw 0x0109805500000000 0x0010980550000000 0x0019800f80000001 0x00019800f8000000

def z358 : W := mkw 0x0416854e9169aa71 0x80416854e9169aa7 0xfc1f8fcff9fffe7f 0xffc1f8fcff9fffe7

def z359 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0xff198fffffc7ffff 0xfff198fffffc7fff

def z360 : W := mkw 0x0000010280408841 0x8000001028040884 0x4000030380009800 0x0400003038000980

def z361 : W := mkw 0x00400aa000005506 0x000400aa00000550 0x000000f000000780 0x0000000f00000078

def z362 : W := mkw 0x2fbd5102fff68849 0x82fbd5102fff6884 0xeffff303ffff980d 0xfeffff303ffff980

def z363 : W := mkw 0x2fbf54087fbe2028 0x02fbf54087fbe202 0xbffffc0c7fff607f 0xfbffffc0c7fff607

def z364 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x530180ff8e0787f2 0x8530180ff8e0787f

def z365 : W := mkw 0x0bc98af582c582d1 0x40bc98af582c582d 0x7ff98fff8fc787ff 0xf7ff98fff8fc787f

def z366 : W := mkw 0x243410007fb60008 0x0243410007fb6000 0xac1e00007fff000d 0x7ac1e00007fff000

def z367 : W := mkw 0x6be9faf56e960008 0x06be9faf56e96000 0x03e1f0f00e070000 0x803e1f0f00e07000

def z368 : W := mkw 0x0109001102840080 0x4010900110284008 0x0300003006000180 0x0030000300600018

def z369 : W := mkw 0x0aa000006c000000 0x00aa000006c00000 0x03e000000e000000 0x803e000000e00000

def z370 : W := mkw 0x10201000d97bee75 0xa10201000d97bee7 0xb000000079fffe7c 0x0b000000079fffe7

def z371 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xfffff0f07fff878f 0xffffff0f07fff878

def z372 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0x6c1e030fb1f89879 0x26c1e030fb1f8987

def z373 : W := mkw 0x04560faa9168fd67 0x804560faa9168fd6 0xfc1e0ffff1f8ffff 0x7fc1e0ffff1f8fff

def z374 : W := mkw 0x0ef40aa07d205506 0x00ef40aa07d20550 0xfffe0ff07ff8ff8f 0xffffe0ff07ff8ff8

def z375 : W := mkw 0x1060b8c448134614 0x21060b8c44813461 0xa0e7f0c0483f0605 0xda0e7f0c0483f060

def z376 : W := mkw 0x006088c448014614 0x0006088c44801461 0xb0e18ccc48076677 0xdb0e18ccc4807667

def z377 : W := mkw 0x0456adce00000000 0x00456adce0000000 0x4cffffcf80000003 0xf4cffffcf8000000

def z378 : W := mkw 0x1060b8c4481b6634 0x21060b8c4481b663 0xb0e1f0c0483f6674 0x8b0e1f0c0483f667

def z379 : W := mkw 0x3fff7c887fbe642c 0x23fff7c887fbe642 0xaffffc007fff600d 0xfaffffc007fff600

def z380 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x9ce00f007e00ff8c 0x49ce00f007e00ff8

def z381 : W := mkw 0x5ef67faa481a6424 0x25ef67faa481a642 0x8ce67f0040386000 0x48ce67f004038600

def z382 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x9ce00fc078007e06 0xd9ce00fc078007e0

def z383 : W := mkw 0x4ac2afff00000000 0x04ac2afff0000000 0x4fe00fff80000002 0xf4fe00fff8000000

def z384 : W := mkw 0x4fffffff48120000 0x04fffffff4812000 0xefffffffc83f0007 0xfefffffffc83f000

def z385 : W := mkw 0x414bafff82c582d1 0x4414bafff82c582d 0x73198fff8fc787ff 0xb73198fff8fc787f

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x500000f000008782 0x0500000f00000878

def z387 : W := mkw 0x0020100048120000 0x0002010004812000 0x80e6700040380000 0x480e670004038000

def z388 : W := mkw 0x00420faa8048fd67 0x800420faa8048fd6 0x50000fff8000fff2 0x050000fff8000fff

def z389 : W := mkw 0x0040088000004404 0x0004008800000440 0x10000cc000006602 0x010000cc00000660

def z390 : W := mkw 0x4f9fe77f00000000 0x04f9fe77f0000000 0x4f1ff33f80000001 0x24f1ff33f8000000

def z391 : W := mkw 0x1062bcddc85be6f5 0x61062bcddc85be6f 0xf0e7fcffc83fe7f7 0xdf0e7fcffc83fe7f

def z392 : W := mkw 0x0eb6050afd68a861 0x80eb6050afd68a86 0xfffe0f0ffff8f87f 0xffffe0f0ffff8f87

def z393 : W := mkw 0x3062bccc7fbf663c 0x23062bccc7fbf663 0xb0e7fccc7fff667f 0xdb0e7fccc7fff667

def z394 : W := mkw 0x4ac06aa000000000 0x04ac06aa00000000 0x00e0700000000000 0x000e070000000000

def z395 : W := mkw 0x1042acdd8049e6f5 0x61042acdd8049e6f 0x50000cff8000e7f2 0x050000cff8000e7f

def z396 : W := mkw 0x051d815793e58ad1 0xc051d815793e58ad 0x7f1983ffbfc79fff 0xb7f1983ffbfc79ff

def z397 : W := mkw 0x00000000804182d1 0x400000000804182d 0x10000000000087f0 0x010000000000087f

def z398 : W := mkw 0x1002a44c00092230 0x21002a44c0009223 0x0000000c00000070 0x00000000c0000007

def z399 : W := mkw 0x1ae2bccc6c1b6634 0x21ae2bccc6c1b663 0xbfe7fccc7e3f667f 0xfbfe7fccc7e3f667

def z400 : W := mkw 0x2fbd50007fb6550e 0x02fbd50007fb6550 0xbffff0007fffff8d 0xfbffff0007fffff8

def z401 : W := mkw 0x2fbdd0557fb60008 0x02fbdd0557fb6000 0xeffff0ffffff000f 0xfeffff0ffffff000

def z402 : W := mkw 0x0f9d400002840000 0x00f9d40000284000 0x2ffff0000fc7000d 0xf2ffff0000fc7000

def z403 : W := mkw 0x4042afff00000000 0x04042afff0000000 0x40e7ffff80000003 0xd40e7ffff8000000

def z404 : W := mkw 0x4ed66faa00000000 0x04ed66faa0000000 0x4cfe7f0f80000003 0x74cfe7f0f8000000

def z405 : W := mkw 0x212910007fb60008 0x0212910007fb6000 0xa31980007fff000d 0xba31980007fff000

def z406 : W := mkw 0x0bc98af500000000 0x00bc98af50000000 0x4ff98fff80000003 0xf4ff98fff8000000

def z407 : W := mkw 0x00620c8848086424 0x000620c884808642 0xb0e60ccc48386677 0xdb0e60ccc4838667

def z408 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xcfe00f307600f988 0x6cfe00f307600f98

def z409 : W := mkw 0x4f9fe55f00000000 0x04f9fe55f0000000 0x0ffff00f80000001 0xf0ffff00f8000000

def z410 : W := mkw 0x110bb45d82dfa2f1 0x6110bb45d82dfa2f 0x201ff00f81ff0071 0x0201ff00f81ff007

def z411 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xcfe00ff070007802 0xfcfe00ff07000780

def z412 : W := mkw 0x0a80022024001102 0x00a8002202400110 0xdf000f307600f98e 0x7df000f307600f98

def z413 : W := mkw 0x2be95aa06e96550e 0x02be95aa06e96550 0x03e1f0f00e070780 0x803e1f0f00e07078

def z414 : W := mkw 0x6fffffff6e960008 0x06fffffff6e96000 0x4fffffff8e070003 0xf4fffffff8e07000

def z415 : W := mkw 0x2fbd40007fa40008 0x02fbd40007fa4000 0x8ff800007fc0000c 0xf8ff800007fc0000

def z416 : W := mkw 0x116bbccc4a9f6634 0x2116bbccc4a9f663 0xb3fffccc4fff667f 0xfb3fffccc4fff667

def z417 : W := mkw 0x0aa002206c001102 0x00aa002206c00110 0xcfe003307e00998c 0xfcfe003307e00998

def z418 : W := mkw 0x0ae00aa048004404 0x00ae00aa04800440 0xdfe00ff048006606 0xfdfe00ff04800660

def z419 : W := mkw 0x0000804400010210 0x0000080440001021 0x000180c008070600 0x8000180c00807060

def z420 : W := mkw 0x116bbcddcadfe6f5 0x6116bbcddcadfe6f 0xb0fffccfc9ff6677 0xdb0fffccfc9ff667

def z421 : W := mkw 0x4ed66faa00000000 0x04ed66faa0000000 0x4fe67ff000000002 0xf4fe67ff00000000

def z422 : W := mkw 0x0ae20faaec48fd67 0x80ae20faaec48fd6 0xdfe00ffffe00fffe 0xfdfe00ffffe00fff

def z423 : W := mkw 0x0aa000006c000000 0x00aa000006c00000 0xdfe000f07e00878e 0xfdfe000f07e00878

def z424 : W := mkw 0x4456afff00000000 0x04456afff0000000 0x4c1e0fff80000003 0x74c1e0fff8000000

def z425 : W := mkw 0x3ffdf8c47fb7461c 0x23ffdf8c47fb7461 0xaffff0c07fff060d 0xfaffff0c07fff060

def z426 : W := mkw 0x0109805580408041 0x0010980558040804 0x731980ff81c0807f 0xb731980ff81c0807

def z427 : W := mkw 0x251f550a93fea869 0x8251f550a93fea86 0x201ff00f81ff0071 0x0201ff00f81ff007

def z428 : W := mkw 0x10623c88481a6424 0x210623c88481a642 0xa0e7fc00483f6005 0xda0e7fc00483f600

def z429 : W := mkw 0x1060b8c448134614 0x21060b8c44813461 0x90e1fcc048076606 0xd90e1fcc04807660

def z430 : W := mkw 0x0002040800082020 0x0000204080008202 0x10000c0c00006072 0x010000c0c0000607

def z431 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x53e00ff00e00ff82 0x853e00ff00e00ff8

def z432 : W := mkw 0x010b855f82cdaaf1 0xc010b855f82cdaaf 0x73198fff8fc7ffff 0xb73198fff8fc7fff

def z433 : W := mkw 0x0b89400000000000 0x00b8940000000000 0x03e1f00000000000 0x803e1f0000000000

def z434 : W := mkw 0x4be9eaf56c005506 0x04be9eaf56c00550 0x03e1f0f00e000780 0x803e1f0f00e00078

def z435 : W := mkw 0x2fbd5000fff68049 0x02fbd5000fff6804 0xfffff00fffff807f 0xffffff00fffff807

def z436 : W := mkw 0x0000000080408041 0x0000000008040804 0x4018000381c08008 0x24018000381c0800

def z437 : W := mkw 0x0ed60faa00000000 0x00ed60faa0000000 0x4ffe0fff80000003 0xf4ffe0fff8000000

def z438 : W := mkw 0x2fbd5000fffea869 0x82fbd5000fffea86 0xbffff0007ffff87d 0xfbffff0007ffff87

def z439 : W := mkw 0x0109805500010210 0x0010980550001021 0x731980ff88070677 0xb731980ff8807067

def z440 : W := mkw 0x3fbd50007fbf663c 0x23fbd50007fbf663 0xbffff0007fff667d 0xfbffff0007fff667

def z441 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0x80e7fcc0483f6600 0xc80e7fcc0483f660

def z442 : W := mkw 0x00422c8800000000 0x000422c880000000 0x00e67c0000000000 0x400e67c000000000

def z443 : W := mkw 0x3ef6fccc7d3b663c 0x23ef6fccc7d3b663 0xbce7fccc783f6677 0xdbce7fccc783f667

def z444 : W := mkw 0x4fdfefff82c480c1 0x44fdfefff82c480c 0x4fffffff87c0818b 0xf4fffffff87c0818

def z445 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0x23fff0000fff0001 0x823fff0000fff000

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0xa006000040380005 0x5a00600004038000

def z447 : W := mkw 0x0e940322b5609943 0x80e940322b560994 0x4f180333b7c09988 0x24f180333b7c0998

def z448 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x8fe00ff07e007f80 0xc8fe00ff07e007f8

def z449 : W := mkw 0x1ae2beec6c1b7736 0x21ae2beec6c1b773 0xbce7ffcc783f7e77 0xdbce7ffcc783f7e7

def z450 : W := mkw 0x0000804400000000 0x0000080440000000 0x000180cc00000003 0x9000180cc0000000

def z451 : W := mkw 0x01299055cad782d1 0x401299055cad782d 0xf3fff0ffcfff87ff 0xff3fff0ffcfff87f

def z452 : W := mkw 0x0ae01aa06c125506 0x00ae01aa06c12550 0xffe7fff07e3fff8f 0xfffe7fff07e3fff8

def z453 : W := mkw 0x1456adce9169ee75 0xa1456adce9169ee7 0xfc1e0fcff1f8fe7f 0x7fc1e0fcff1f8fe7

def z454 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0x8fe7f0007e3f0000 0xc8fe7f0007e3f000

def z455 : W := mkw 0x1060388048124404 0x2106038804812440 0x00e0700000000000 0x000e070000000000

def z456 : W := mkw 0x4f9d433391608841 0x84f9d43339160884 0x4f180333b1c09808 0x24f180333b1c0980

def z457 : W := mkw 0x2ffd4aa07fa4550e 0x02ffd4aa07fa4550 0xdff80ff07fc0ff8e 0xfdff80ff07fc0ff8

def z458 : W := mkw 0x0002855f8049aaf1 0xc0002855f8049aaf 0x50000fff8000fff2 0x050000fff8000fff

def z459 : W := mkw 0x0414000011200000 0x0041400001120000 0x0c18000031c00008 0x20c18000031c0000

def z460 : W := mkw 0x0ef60faa7d287d26 0x80ef60faa7d287d2 0xdfe60ff07e38ff8e 0xfdfe60ff07e38ff8

def z461 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xbc060f0071f8f87c 0x4bc060f0071f8f87

def z462 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x7019800f81c7807f 0x37019800f81c7807

def z463 : W := mkw 0x0be98af56c005506 0x00be98af56c00550 0xdff98ffffe00ff8f 0xfdff98ffffe00ff8

def z464 : W := mkw 0x4042afff00005506 0x04042afff0000550 0x50000fff8000ff82 0x050000fff8000ff8

def z465 : W := mkw 0x4fdfefff02850290 0x44fdfefff0285029 0x4fffffff8e070783 0xf4fffffff8e07078

def z466 : W := mkw 0x1169b8d54a974694 0x61169b8d54a97469 0x03e1f0f00e070780 0x803e1f0f00e07078

def z467 : W := mkw 0x0109000000000000 0x0010900000000000 0x0319800000000001 0xb031980000000000

def z468 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x431980f38fc78788 0xa431980f38fc7878

def z469 : W := mkw 0x000000009168a861 0x8000000009168a86 0x2000000001f80070 0x02000000001f8007

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000c008000606 0x9100000c00800060

def z471 : W := mkw 0x0109001182c480c1 0x40109001182c480c 0x0018000381c00000 0x00018000381c0000

def z472 : W := mkw 0x0040088000000000 0x0004008800000000 0x00e00cc000000002 0xd00e00cc00000000

def z473 : W := mkw 0x0ac00aa000005506 0x00ac00aa00000550 0x5fe00ff00000ff82 0xf5fe00ff00000ff8

def z474 : W := mkw 0x0416050a11282820 0x80416050a1128282 0xdc060f007038f80e 0x7dc060f007038f80

def z475 : W := mkw 0x4f9f473b00000000 0x04f9f473b0000000 0x4f1e0f3f80000003 0x74f1e0f3f8000000

def z476 : W := mkw 0x2fbfd55fffffaaf9 0xc2fbfd55fffffaaf 0xffffffffffffffff 0xffffffffffffffff

def z477 : W := mkw 0x051f855f93edaaf1 0xc051f855f93edaaf 0xfc1f8f0ff1fff87f 0x7fc1f8f0ff1fff87

def z478 : W := mkw 0x251dd05593f782d9 0x4251dd05593f782d 0x731ff0ff8fff87ff 0xb731ff0ff8fff87f

def z479 : W := mkw 0x6fbff55f7fb60008 0x06fbff55f7fb6000 0xaffff00fffff000d 0xfaffff00fffff000

def z480 : W := mkw 0x6f9d433337a40008 0x06f9d433337a4000 0x4f180333b7c00008 0x24f180333b7c0000

def z481 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x8fe00f007e00780c 0xf8fe00f007e00780

def z482 : W := mkw 0x114bacdd82cde6f5 0x6114bacdd82cde6f 0x73198cff8fc7e7ff 0xb73198cff8fc7e7f

def z483 : W := mkw 0x2fbd50006e960008 0x02fbd50006e96000 0x0ffff0000e070001 0xf0ffff0000e07000

def z484 : W := mkw 0x0e96072ab568b963 0x80e96072ab568b96 0xff1e0f3ff7f8f9ff 0x7ff1e0f3ff7f8f9f

def z485 : W := mkw 0x4fdfefff00010210 0x04fdfefff0001021 0x7fffffff88070677 0xf7fffffff8807067

def z486 : W := mkw 0x0eb400007d200000 0x00eb400007d20000 0xaffe00007ff8000d 0xfaffe00007ff8000

def z487 : W := mkw 0x0ae008806c004404 0x00ae008806c00440 0x9fe00cc07e00660e 0xf9fe00cc07e00660

def z488 : W := mkw 0x10623c88481a6424 0x210623c88481a642 0xb0e67c0c40386077 0x5b0e67c0c4038607

def z489 : W := mkw 0x0060088048004404 0x0006008804800440 0xdce00fc07800fe0e 0xfdce00fc07800fe0

def z490 : W := mkw 0x1ae0bae46c135716 0x21ae0bae46c13571 0x03e1f0f00e070780 0x803e1f0f00e07078

def z491 : W := mkw 0x2f9d422037a4110a 0x02f9d422037a4110 0x4f18033037c09988 0x24f18033037c0998

def z492 : W := mkw 0x0000000000005506 0x0000000000000550 0x100000000000ff80 0x0100000000000ff8

def z493 : W := mkw 0x0aa002206c005506 0x00aa002206c00550 0xdf0003307e00ff8c 0x2df0003307e00ff8

def z494 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018000f80000003 0x34018000f8000000

def z495 : W := mkw 0x4042afff804182d1 0x44042afff804182d 0x50000fff800087f2 0x050000fff800087f

def z496 : W := mkw 0x0000000091608841 0x8000000009160884 0x0000000031c09808 0x00000000031c0980

def z497 : W := mkw 0x351ff44c13bf2238 0x2351ff44c13bf223 0x201ff00c01ff0071 0x0201ff00c01ff007

def z498 : W := mkw 0x1000000000096634 0x2100000000009663 0x1000000000006670 0x0100000000000667

def z499 : W := mkw 0x016988d5cac5c6d5 0x4016988d5cac5c6d 0xf3f98cffcfc7e7ff 0xff3f98cffcfc7e7f

def z500 : W := mkw 0x0aa010006c120000 0x00aa010006c12000 0xafe7f0007e3f000d 0xfafe7f0007e3f000

def z501 : W := mkw 0x1062accc48096634 0x21062accc4809663 0x90e00ccc48006676 0xd90e00ccc4800667

def z502 : W := mkw 0x051d000013a40000 0x0051d000013a4000 0xaf1f80007fff000d 0xfaf1f80007fff000

def z503 : W := mkw 0x10001000001b2230 0x210001000001b223 0x20000000003f0070 0x020000000003f007

def z504 : W := mkw 0x0ef60faa6c005506 0x00ef60faa6c00550 0xdffe0ffffe00ff8f 0xfdffe0ffffe00ff8

def z505 : W := mkw 0x0109805582c480c1 0x40109805582c480c 0x431980ff87c0818b 0xb431980ff87c0818

def z506 : W := mkw 0x0416050a80408041 0x00416050a8040804 0x7c1e0f0f81c0807f 0x77c1e0f0f81c0807

def z507 : W := mkw 0x451fe55f82c582d1 0x4451fe55f82c582d 0x201ff00f81c70071 0x0201ff00f81c7007

def z508 : W := mkw 0x2e94400035200008 0x02e9440003520000 0x0c00000030000000 0x00c0000003000000

def z509 : W := mkw 0x0000000011200000 0x0000000001120000 0xa000000071f8000c 0x0a000000071f8000

def z510 : W := mkw 0x2f9d400037a40008 0x02f9d400037a4000 0x0ffff00037c00009 0xf0ffff00037c0000

def z511 : W := mkw 0x0be98af56e855796 0x40be98af56e85579 0x03e180f00e070780 0x803e180f00e07078

def z512 : W := mkw 0x3fbff44c7fbf2238 0x23fbff44c7fbf223 0xaffff00c7fff007d 0xfaffff00c7fff007

def z513 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0x701e0f0f81f8f873 0x0701e0f0f81f8f87

def z514 : W := mkw 0x0020100048120000 0x0002010004812000 0xa0000000483f0004 0x0a0000000483f000

def z515 : W := mkw 0x302010007fbf663c 0x2302010007fbf663 0xb00000007fff667c 0x0b00000007fff667

def z516 : W := mkw 0x2aa050006c120008 0x02aa050006c12000 0x00e0700000000000 0x000e070000000000

def z517 : W := mkw 0x00000011804080c1 0x400000011804080c 0x4000003380008180 0x0400000338000818

def z518 : W := mkw 0x1416b54e917baa71 0xa1416b54e917baa7 0x201ff00f81ff0071 0x0201ff00f81ff007

def z519 : W := mkw 0x2f9f450ab7eca869 0x82f9f450ab7eca86 0xff1e0f0ff7f8f87f 0x7ff1e0f0ff7f8f87

def z520 : W := mkw 0x00008055804182d1 0x400008055804182d 0x701800ff81c087ff 0x3701800ff81c087f

def z521 : W := mkw 0x251d500013b60008 0x0251d500013b6000 0xac1ff00071ff000d 0x7ac1ff00071ff000

def z522 : W := mkw 0x0109805502850290 0x4010980550285029 0x431980ff8e070783 0xb431980ff8e07078

def z523 : W := mkw 0x4000033300000000 0x0400003330000000 0x4000033380000000 0x0400003338000000

def z524 : W := mkw 0x00600aa048005506 0x000600aa04800550 0xd0e00ff04800ff86 0xdd0e00ff04800ff8

def z525 : W := mkw 0x4fddeaf500000000 0x04fddeaf50000000 0x0ffff0f000000001 0xf0ffff0f00000000

def z526 : W := mkw 0x0b890231a6c491c3 0x40b890231a6c491c 0x4f180333b7c09988 0x24f180333b7c0998

def z527 : W := mkw 0x2fff5faafffefd6f 0x82fff5faafffefd6 0xffffffffffffffff 0xffffffffffffffff

def z528 : W := mkw 0x1476bdced97bee75 0xa1476bdced97bee7 0xb0fffccfc9ff6677 0xdb0fffccfc9ff667

def z529 : W := mkw 0x4bcbeefd00000000 0x04bcbeefd0000000 0x03e7fcfc00000003 0xd03e7fcfc0000000

def z530 : W := mkw 0x051f855f00000000 0x0051f855f0000000 0x4f1f8fff80000003 0xf4f1f8fff8000000

def z531 : W := mkw 0x0000000080408041 0x0000000008040804 0x3000000001c0807c 0x03000000001c0807

def z532 : W := mkw 0x2ba950006e960008 0x02ba950006e96000 0xa3e7f0004e3f0005 0xda3e7f0004e3f000

def z533 : W := mkw 0x0109000002840000 0x0010900000284000 0x030180000e070000 0x8030180000e07000

def z534 : W := mkw 0x2ba9d0556e970298 0x42ba9d0556e97029 0x03e1f0f00e070780 0x803e1f0f00e07078

def z535 : W := mkw 0x4ffd4bb36c005506 0x04ffd4bb36c00550 0xdff80ff3fe00ff8e 0xfdff80ff3fe00ff8

def z536 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x00e0000000000000 0x000e000000000000

def z537 : W := mkw 0x1476bdce593b6e34 0xa1476bdce593b6e3 0xbce7ffcc783f7e77 0xdbce7ffcc783f7e7

def z538 : W := mkw 0x2ba9d055eed782d9 0x42ba9d055eed782d 0x73f9f0ff8fc787ff 0xb73f9f0ff8fc787f

def z539 : W := mkw 0x0414010291608841 0x8041401029160884 0xdc180f03f1c0f80e 0x7dc180f03f1c0f80

def z540 : W := mkw 0x0109804402850210 0x0010980440285021 0x331980cc0fc7067f 0xb331980cc0fc7067

def z541 : W := mkw 0x4fdfefff80408041 0x04fdfefff8040804 0x7fffffff81c0807f 0xf7fffffff81c0807

def z542 : W := mkw 0x0be90aa06e845506 0x00be90aa06e84550 0xfff98ff07fc7ff8f 0xffff98ff07fc7ff8

def z543 : W := mkw 0x4ed66faa9168a861 0x84ed66faa9168a86 0xfcfe7f0ff1f8f87f 0x7fcfe7f0ff1f8f87

def z544 : W := mkw 0x1ae23ea86c1a7526 0x21ae23ea86c1a752 0x8ce67f0070387800 0x48ce67f007038780

def z545 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x93e000f07e00ff8c 0x893e000f07e00ff8

def z546 : W := mkw 0x000000009168a861 0x8000000009168a86 0xf018000ff1f8f87f 0x3f018000ff1f8f87

def z547 : W := mkw 0x0ed60faa9168a861 0x80ed60faa9168a86 0xfffe0ffff1f8f87f 0xffffe0ffff1f8f87

def z548 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0x8ffe700077f80008 0x68ffe700077f8000

def z549 : W := mkw 0x0000000000010210 0x0000000000001021 0x3000000008070674 0x0300000000807067

def z550 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0x0ff9f0003fc70008 0xa0ff9f0003fc7000

def z551 : W := mkw 0x0ef40ba2fd60dd47 0x80ef40ba2fd60dd4 0xdff80ff3ffc0ff8e 0xfdff80ff3ffc0ff8

def z552 : W := mkw 0x00600aa06c005506 0x000600aa06c00550 0xd0000ff07e00ff8e 0x0d0000ff07e00ff8

def z553 : W := mkw 0x0be98af56e855796 0x40be98af56e85579 0xdfe18ff07e07ff8e 0xfdfe18ff07e07ff8

def z554 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x330180f00fc787fc 0x8330180f00fc787f

def z555 : W := mkw 0x1042bccc001b6634 0x21042bccc001b663 0x3007fccc003f6673 0x03007fccc003f667

def z556 : W := mkw 0x1bebbefdeedff7f7 0x61bebbefdeedff7f 0xffffffffffffffff 0xffffffffffffffff

def z557 : W := mkw 0x4456afff9168a861 0x84456afff9168a86 0xfc1e0ffff1f8f87f 0x7fc1e0ffff1f8f87

def z558 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x8fe000f07e00078c 0xf8fe000f07e00078

def z559 : W := mkw 0x1062bcccd97bee75 0xa1062bcccd97bee7 0xb0e7fccc79fffe7f 0xdb0e7fccc79fffe7

def z560 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xac1e000ff1f8007d 0x7ac1e000ff1f8007

def z561 : W := mkw 0x116bbcdd4a9f66b4 0x6116bbcdd4a9f66b 0xb3e7fcfc4e3f67f7 0xdb3e7fcfc4e3f67f

def z562 : W := mkw 0x00400aa000000000 0x000400aa00000000 0x40000ff000000002 0x040000ff00000000

def z563 : W := mkw 0x0f9dc05582c582d1 0x40f9dc05582c582d 0x7ffff0ff8fc787ff 0xf7ffff0ff8fc787f

def z564 : W := mkw 0x2109500002960008 0x0210950000296000 0x0001f00000070000 0x00001f0000007000

def z565 : W := mkw 0x01498af582c5d7d7 0x401498af582c5d7d 0x73198fff8fc7ffff 0xb73198fff8fc7fff

def z566 : W := mkw 0x557ffddf481b6634 0x2557ffddf481b663 0xb0fffccfc83f6677 0xdb0fffccfc83f667

def z567 : W := mkw 0x000204088048a061 0x0000204088048a06 0xf01e0c0fc1f8e07f 0x7f01e0c0fc1f8e07

def z568 : W := mkw 0x0002040800000000 0x0000204080000000 0x00060c0c00000003 0x500060c0c0000000

def z569 : W := mkw 0x00400aa000005506 0x000400aa00000550 0xdc000ff07000ff8e 0x7dc000ff07000ff8

def z570 : W := mkw 0x0414010291608841 0x8041401029160884 0xec1e0303f1f8980d 0x7ec1e0303f1f8980

def z571 : W := mkw 0x357ffccc5bbf663c 0x2357ffccc5bbf663 0xb0fffccc49ff6677 0xdb0fffccc49ff667

def z572 : W := mkw 0x0ae2aeec6c005506 0x00ae2aeec6c00550 0xdfe7fffc7e00ff8f 0xfdfe7fffc7e00ff8

def z573 : W := mkw 0x1002b44c001b2230 0x21002b44c001b223 0x3007f0cc083f0677 0x93007f0cc083f067

def z574 : W := mkw 0x0ac00aa000000000 0x00ac00aa00000000 0x0ce00f0000000000 0x40ce00f000000000

def z575 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x6319803f87c781f9 0x26319803f87c781f

def z576 : W := mkw 0x0000804400010210 0x0000080440001021 0x730180fc0e0787ff 0xb730180fc0e0787f

def z577 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000c00000077 0x13000000c0000007

def z578 : W := mkw 0x451fe55f00000000 0x0451fe55f0000000 0x431ff0ff80000003 0xb431ff0ff8000000

def z579 : W := mkw 0x0a80000024000000 0x00a8000002400000 0x0f00000036000008 0x20f0000003600000

def z580 : W := mkw 0x1476bccc593b6634 0x21476bccc593b663 0xbcfffccc79ff667f 0xfbcfffccc79ff667

def z581 : W := mkw 0x0000805582c582d1 0x40000805582c582d 0x700000ff8fc787fe 0x0700000ff8fc787f

def z582 : W := mkw 0x4416650a00000000 0x04416650a0000000 0x0006700000000000 0x0000670000000000

def z583 : W := mkw 0x3ffffcddffffe6fd 0x63ffffcddffffe6f 0xfffffcffffffe7ff 0xffffffcffffffe7f

def z584 : W := mkw 0x202010006e960008 0x0202010006e96000 0x000000000e070000 0x0000000000e07000

def z585 : W := mkw 0x051d400000000000 0x0051d40000000000 0x001ff00000000001 0x0001ff0000000000

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0x030000f00e000780 0x8030000f00e00078

def z587 : W := mkw 0x0416050a11282820 0x80416050a1128282 0xbc060f0c70387877 0x5bc060f0c7038787

def z588 : W := mkw 0x1ae2beec6c1b7736 0x21ae2beec6c1b773 0xb3e7fcfc4e3f67f7 0xdb3e7fcfc4e3f67f

def z589 : W := mkw 0x0ef60faafd68fd67 0x80ef60faafd68fd6 0xfcfe0f0ff1f8f87f 0x7fcfe0f0ff1f8f87

def z590 : W := mkw 0x4040aaf500000000 0x04040aaf50000000 0x000000f000000000 0x0000000f00000000

def z591 : W := mkw 0x2ba950007fb60008 0x02ba950007fb6000 0xa3e1f0007fff000c 0x8a3e1f0007fff000

def z592 : W := mkw 0x0416050a11200000 0x00416050a1120000 0xec1e0f0ff1f8000f 0x7ec1e0f0ff1f8000

def z593 : W := mkw 0x5be9faf548134614 0x25be9faf54813461 0x03e1f0f008070600 0x803e1f0f00807060

def z594 : W := mkw 0x0000100000120000 0x0000010000012000 0x2007f000003f0001 0x02007f000003f000

def z595 : W := mkw 0x0109001182c582d1 0x40109001182c582d 0x731800338fc787fc 0x2731800338fc787f

def z596 : W := mkw 0x0002a44c00000000 0x00002a44c0000000 0x0007f00c00000001 0x00007f00c0000000

def z597 : W := mkw 0x10601880481b6634 0x210601880481b663 0xb0e00cc0483f6676 0xdb0e00cc0483f667

def z598 : W := mkw 0x0456adce9168a861 0x80456adce9168a86 0xfcffffcff1f8f87f 0xffcffffcff1f8f87

def z599 : W := mkw 0x551ff55f001b2230 0x2551ff55f001b223 0x201ff00f803f0071 0x0201ff00f803f007

def z600 : W := mkw 0x0000000082c480c1 0x40000000082c480c 0x0000000007c08188 0x00000000007c0818

def z601 : W := mkw 0x0f9dc05500000000 0x00f9dc0550000000 0x4ffff0ff80000003 0xf4ffff0ff8000000

def z602 : W := mkw 0x2ef45aa07d32550e 0x02ef45aa07d32550 0xdfe67ff07e38ff8e 0xfdfe67ff07e38ff8

def z603 : W := mkw 0x0a80022024001102 0x00a8002202400110 0x0300003006000180 0x0030000300600018

def z604 : W := mkw 0x2000000037a40008 0x02000000037a4000 0x0000000037c00008 0x00000000037c0000

def z605 : W := mkw 0x11299055cadfe6f5 0x611299055cadfe6f 0xf31980ffcfffe7ff 0xbf31980ffcfffe7f

def z606 : W := mkw 0x0416050a11282820 0x80416050a1128282 0xac1e0f0071f8780d 0x7ac1e0f0071f8780

def z607 : W := mkw 0x0000000024001102 0x0000000002400110 0x0000000036009988 0x0000000003600998

def z608 : W := mkw 0x4f9f473b9168a861 0x84f9f473b9168a86 0xff1e0f3ff1f8f87f 0x7ff1e0f3ff1f8f87

def z609 : W := mkw 0x202010007d320008 0x0202010007d32000 0x8000000070380000 0x0800000007038000

def z610 : W := mkw 0x14763d8a593a6c24 0xa14763d8a593a6c2 0x8ce67f0070387800 0x48ce67f007038780

def z611 : W := mkw 0x000204089168a861 0x8000204089168a86 0xb0060c0c71f8f87f 0x5b0060c0c71f8f87

def z612 : W := mkw 0x0f9f450a9168a861 0x80f9f450a9168a86 0xffffff0ff1f8f87f 0xfffffff0ff1f8f87

def z613 : W := mkw 0x0000000002850290 0x4000000000285029 0x000000000e070780 0x0000000000e07078

def z614 : W := mkw 0x5fffffffcadfe6f5 0x65fffffffcadfe6f 0xffffffffcfffe7ff 0xfffffffffcfffe7f

def z615 : W := mkw 0x6fdfffff13b60008 0x06fdfffff13b6000 0x6fffffff81ff0003 0xf6fffffff81ff000

def z616 : W := mkw 0x1022b44c481b6634 0x21022b44c481b663 0xb007f00c483f6675 0x0b007f00c483f667

def z617 : W := mkw 0x0416050a00000000 0x00416050a0000000 0xdc1e0f0ff000f80f 0x7dc1e0f0ff000f80

def z618 : W := mkw 0x0be90ab1eec4d5c7 0x40be90ab1eec4d5c 0xdff80ff3ffc0ff8e 0xfdff80ff3ffc0ff8

def z619 : W := mkw 0x002000006c005506 0x0002000006c00550 0xdc000f007e00ff8e 0x7dc000f007e00ff8

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z621 : W := mkw 0x2ba950006e960008 0x02ba950006e96000 0x8fe1f0007e07000c 0xf8fe1f0007e07000

def z622 : W := mkw 0x010b845d82cda2f1 0x4010b845d82cda2f 0xf31f8cffcfffe7ff 0xff31f8cffcfffe7f

def z623 : W := mkw 0x0109001182c480c1 0x40109001182c480c 0x7318003f87c081ff 0x37318003f87c081f

def z624 : W := mkw 0x6fffffff7fb6550e 0x06fffffff7fb6550 0xffffffffffffff8f 0xfffffffffffffff8

def z625 : W := mkw 0x0fdfeccc00000000 0x00fdfeccc0000000 0x0ffffccc00000003 0xf0ffffccc0000000

def z626 : W := mkw 0x0002050a00082820 0x80002050a0008282 0x00000f0000007800 0x000000f000000780

def z627 : W := mkw 0x0060088048004404 0x0006008804800440 0x80e00c0040006000 0x480e00c004000600

def z628 : W := mkw 0x051f855f82c582d1 0x4051f855f82c582d 0x7f1f8fff8fc787ff 0xf7f1f8fff8fc787f

def z629 : W := mkw 0x0042accc00082020 0x00042accc0008202 0xb0e7fccc40386077 0xdb0e7fccc4038607

def z630 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x4fe00ff00e000782 0xf4fe00ff00e00078

def z631 : W := mkw 0x0020000048004404 0x0002000004800440 0x9000000048006604 0x0900000004800660

def z632 : W := mkw 0x0fdd4aa000000000 0x00fdd4aa00000000 0x4ffffff000000003 0xf4ffffff00000000

def z633 : W := mkw 0x01298055eec5d7d7 0x401298055eec5d7d 0xf31980ffffc7ffff 0xbf31980ffffc7fff

def z634 : W := mkw 0x00200000eec5d7d7 0x400200000eec5d7d 0xb00000007fc7fffc 0x0b00000007fc7fff

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c000f0000000002 0x74c000f000000000

def z636 : W := mkw 0x0414000011200000 0x0041400001120000 0x201e000001f80001 0x0201e000001f8000

def z637 : W := mkw 0x2ffd5aa07fb60008 0x02ffd5aa07fb6000 0xeffffff07fff000f 0xfeffffff07fff000

def z638 : W := mkw 0x4f9d433324001102 0x04f9d43332400110 0x4f180333b6009988 0x24f180333b600998

def z639 : W := mkw 0x1ae2aeec6c097736 0x21ae2aeec6c09773 0xdfe00ffc7e00fffe 0xfdfe00ffc7e00fff

def z640 : W := mkw 0x0416050a00000000 0x00416050a0000000 0x0c060f0000000000 0x40c060f000000000

def z641 : W := mkw 0x10623c88481b6634 0x210623c88481b663 0xb0e67c00483f6674 0x4b0e67c00483f667

def z642 : W := mkw 0x3be9f8c46e97461c 0x23be9f8c46e97461 0x03e1f0c00e070600 0x803e1f0c00e07060

def z643 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0x701e000f81f8807f 0x3701e000f81f8807

def z644 : W := mkw 0x4b89423100000000 0x04b8942310000000 0x0300003000000000 0x0030000300000000

def z645 : W := mkw 0x1169b8d5cad7c6d5 0x61169b8d5cad7c6d 0x73f9f0ff8fc787ff 0xb73f9f0ff8fc787f

def z646 : W := mkw 0x0416050a93edaaf1 0xc0416050a93edaaf 0xfc1e0f0fffffffff 0x7fc1e0f0ffffffff

def z647 : W := mkw 0x0a80022024001102 0x00a8002202400110 0x0c00030030001800 0x00c0003003000180

def z648 : W := mkw 0x0ba900006e840000 0x00ba900006e84000 0xaff980007fc7000d 0xfaff980007fc7000

def z649 : W := mkw 0x0109805502840000 0x0010980550284000 0x631980ff8fc7000f 0xb631980ff8fc7000

def z650 : W := mkw 0x0002050a8048a861 0x80002050a8048a86 0xf0060f0fc038f877 0x5f0060f0fc038f87

def z651 : W := mkw 0x0f9d400000000000 0x00f9d40000000000 0x0f18000000000000 0x20f1800000000000

def z652 : W := mkw 0x6ef67faa7d320008 0x06ef67faa7d32000 0x8ce67f0070380000 0x48ce67f007038000

def z653 : W := mkw 0x4ed6efee00000000 0x04ed6efee0000000 0x0ce7ffcc00000003 0xd0ce7ffcc0000000

def z654 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x2319800f8fc7007d 0xb2319800f8fc7007

def z655 : W := mkw 0x0002050a00000000 0x00002050a0000000 0x40000f0f80000002 0x040000f0f8000000

def z656 : W := mkw 0x3ef67c887d3a642c 0x23ef67c887d3a642 0x8ce67c0070386000 0x48ce67c007038600

def z657 : W := mkw 0x4fdfefff93edaaf1 0xc4fdfefff93edaaf 0xffffffffffffffff 0xffffffffffffffff

def z658 : W := mkw 0x00400aa000005506 0x000400aa00000550 0x00000f0000007800 0x000000f000000780

def z659 : W := mkw 0x0000000093edaaf1 0xc0000000093edaaf 0xb00000007ffffffc 0x0b00000007ffffff

def z660 : W := mkw 0x00408af58041d7d7 0x400408af58041d7d 0x50000fff8000fff2 0x050000fff8000fff

def z661 : W := mkw 0x5fffffff481a6424 0x25fffffff481a642 0xcfffffffc0386003 0xfcfffffffc038600

def z662 : W := mkw 0x0436050afd68fd67 0x80436050afd68fd6 0xfc1e0f0ffff8ffff 0x7fc1e0f0ffff8fff

def z663 : W := mkw 0x451fe55f82c582d1 0x4451fe55f82c582d 0x731ff0ff8fc787ff 0xb731ff0ff8fc787f

def z664 : W := mkw 0x0060088048004404 0x0006008804800440 0xd3e00cf04e00e78e 0xfd3e00cf04e00e78

def z665 : W := mkw 0x4109e05500000000 0x04109e0550000000 0x0001f00000000000 0x00001f0000000000

def z666 : W := mkw 0x6ffdfaf57fb60008 0x06ffdfaf57fb6000 0xaffff0f07fff000d 0xfaffff0f07fff000

def z667 : W := mkw 0x0416050a91608841 0x80416050a9160884 0x4c1e0f0fb1c0980b 0x74c1e0f0fb1c0980

def z668 : W := mkw 0x0000804480418251 0x0000080448041825 0x701980cf89c7867f 0xb701980cf89c7867

def z669 : W := mkw 0x2eb6550a7d3a2828 0x82eb6550a7d3a282 0x8ce67f0070387800 0x48ce67f007038780

def z670 : W := mkw 0x0a80022000000000 0x00a8002200000000 0x4f00033000000000 0x24f0003300000000

def z671 : W := mkw 0x000000009168a861 0x8000000009168a86 0xfc000f0071f8f87e 0x7fc000f0071f8f87

def z672 : W := mkw 0x2eb6550afd7aa869 0x82eb6550afd7aa86 0xfcfe7f0ff1f8f87f 0x7fcfe7f0ff1f8f87

def z673 : W := mkw 0x051f855f93edaaf1 0xc051f855f93edaaf 0x731f80ff8fff87ff 0xb731f80ff8fff87f

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x2018000001c0000d 0x32018000001c0000

def z675 : W := mkw 0x2fbdd055fff782d9 0x42fbdd055fff782d 0xaffff00fffff007d 0xfaffff00fffff007

def z676 : W := mkw 0x4fffefff6c005506 0x04fffefff6c00550 0x4fffffff8e000783 0xf4fffffff8e00078

def z677 : W := mkw 0x451fe55f00000000 0x0451fe55f0000000 0x4c1fff0f80000003 0x74c1fff0f8000000

def z678 : W := mkw 0x2fbd50007d320008 0x02fbd50007d32000 0x8ffff00070380001 0xf8ffff0007038000

def z679 : W := mkw 0x0ffd4aa06c005506 0x00ffd4aa06c00550 0xdffffff07e00ff8f 0xfdffffff07e00ff8

def z680 : W := mkw 0x2eb450007d320008 0x02eb450007d32000 0xace7f000783f0005 0xdace7f000783f000

def z681 : W := mkw 0x4f9dc37782c582d1 0x44f9dc37782c582d 0x7f1983ff8fc787ff 0xb7f1983ff8fc787f

def z682 : W := mkw 0x0000804400010210 0x0000080440001021 0x2001800c00070071 0x02001800c0007007

def z683 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xb01e0c0fc1f86077 0x5b01e0c0fc1f8607

def z684 : W := mkw 0x051f855f9168a861 0x8051f855f9168a86 0xff1f8ffff1f8f87f 0xfff1f8ffff1f8f87

def z685 : W := mkw 0x2f9dc055b7e582d9 0x42f9dc055b7e582d 0x7f1980ffbfc787ff 0xb7f1980ffbfc787f

def z686 : W := mkw 0x0aa000006c005506 0x00aa000006c00550 0x9fe000007e00ff8c 0xf9fe000007e00ff8

def z687 : W := mkw 0x0ac00aa000000000 0x00ac00aa00000000 0xdfe00ff07000f80e 0xfdfe00ff07000f80

def z688 : W := mkw 0x1436150ad97bee75 0xa1436150ad97bee7 0xfc1e0f0ff9fffe7f 0x7fc1e0f0ff9fffe7

def z689 : W := mkw 0x0436150ad97aa861 0x80436150ad97aa86 0xfcffff0ff9fff87f 0xffcffff0ff9fff87

def z690 : W := mkw 0x0e94400000000000 0x00e9440000000000 0x0ce6700000000000 0x40ce670000000000

def z691 : W := mkw 0x0109805502850290 0x4010980550285029 0x231980f00fc7078d 0xb231980f00fc7078

def z692 : W := mkw 0x0f9d400011200000 0x00f9d40001120000 0xaffff00071f8000d 0xfaffff00071f8000

def z693 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x301980cf89c70677 0x9301980cf89c7067

def z694 : W := mkw 0x0002050a9168a861 0x80002050a9168a86 0xf0000f0ff1f8f87e 0x0f0000f0ff1f8f87

def z695 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x53e000f00e00878e 0xb53e000f00e00878

def z696 : W := mkw 0x00400aa000005506 0x000400aa00000550 0x53000ff00e00ff8e 0xb53000ff00e00ff8

def z697 : W := mkw 0x0020000048000000 0x0002000004800000 0x80e0000048000004 0xd80e000004800000

def z698 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x631980ff81c70073 0xb631980ff81c7007

def z699 : W := mkw 0x0002844c00092230 0x00002844c0009223 0xb0078ccc483f6677 0xdb0078ccc483f667

def z700 : W := mkw 0x2ffd5aa07fb6550e 0x02ffd5aa07fb6550 0xafffff007fff780d 0xfafffff007fff780

def z701 : W := mkw 0x0002050a8048a861 0x80002050a8048a86 0x70180f0f81c0f87f 0x370180f0f81c0f87

def z702 : W := mkw 0x4002a55f00000000 0x04002a55f0000000 0x0000000f80000000 0x00000000f8000000

def z703 : W := mkw 0x1042accc00096634 0x21042accc0009663 0x30018ccc08076677 0x930018ccc0807667

def z704 : W := mkw 0x2eb450007fb60008 0x02eb450007fb6000 0xace670007fff000c 0x4ace670007fff000

def z705 : W := mkw 0x0002040800082020 0x0000204080008202 0x2006000c00380071 0x02006000c0038007

def z706 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4f180fff80000002 0x24f180fff8000000

def z707 : W := mkw 0x055faddf00000000 0x0055faddf0000000 0x4fffffff80000003 0xf4fffffff8000000

def z708 : W := mkw 0x0020904448130210 0x0002090444813021 0xa0e7f00c483f0075 0xda0e7f00c483f007

def z709 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x73198fff8fc7ffff 0xb73198fff8fc7fff

def z710 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0e7fccc403f6673 0x4b0e7fccc403f667

def z711 : W := mkw 0x0ba910006e960000 0x00ba910006e96000 0xaffff0007fff000d 0xfaffff0007fff000

def z712 : W := mkw 0x2fbd50007fb6110a 0x02fbd50007fb6110 0xaffff0007fff998d 0xfaffff0007fff998

def z713 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xec1e0f0ff1f8f879 0x6ec1e0f0ff1f8f87

def z714 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xbc1e0f0ff1f87877 0x5bc1e0f0ff1f8787

def z715 : W := mkw 0x253d50007fb60008 0x0253d50007fb6000 0xa0fff0007fff000d 0xda0fff0007fff000

def z716 : W := mkw 0x1022b44c481b2230 0x21022b44c481b223 0x20e7f00c083f0071 0x820e7f00c083f007

def z717 : W := mkw 0x1042bccc001b2230 0x21042bccc001b223 0x30e7fccc083f0677 0xd30e7fccc083f067

def z718 : W := mkw 0x002010004a960000 0x0002010004a96000 0xa0e7f0004fff000d 0xda0e7f0004fff000

def z719 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xefffff007fff000f 0xfefffff007fff000

def z720 : W := mkw 0x4fdfefff02850210 0x04fdfefff0285021 0x7fffffff8fc7067f 0xf7fffffff8fc7067

def z721 : W := mkw 0x0be98af5eec5d7d7 0x40be98af5eec5d7d 0xacf98f0ff1c77871 0x4acf98f0ff1c7787

def z722 : W := mkw 0x2fbd50007fb6550e 0x02fbd50007fb6550 0xfffff0f07fffff8f 0xffffff0f07fffff8

def z723 : W := mkw 0x1062beec481b7736 0x21062beec481b773 0xb0e7fcfc483f67f7 0xdb0e7fcfc483f67f

def z724 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4ffff3ff80000001 0xa4ffff3ff8000000

def z725 : W := mkw 0x1474b9c6d973ce55 0xa1474b9c6d973ce5 0x4cf9f3c3b9c79e08 0xa4cf9f3c3b9c79e0

def z726 : W := mkw 0x4fdd6bb300000000 0x04fdd6bb30000000 0x4ff8733380000000 0x24ff873338000000

def z727 : W := mkw 0x6fdfefff35200008 0x06fdfefff3520000 0x4fffffffb0000003 0xf4fffffffb000000

def z728 : W := mkw 0x0149a8d500000000 0x00149a8d50000000 0x43f9f0ff80000003 0xb43f9f0ff8000000

def z729 : W := mkw 0x4fdd4bb300000000 0x04fdd4bb30000000 0x4ffffff380000003 0xf4ffffff38000000

def z730 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xfc1e0f0ffff8ffff 0x7fc1e0f0ffff8fff

def z731 : W := mkw 0x1060b8c4481b6634 0x21060b8c4481b663 0xb0e7f0c0483f6675 0xdb0e7f0c0483f667

def z732 : W := mkw 0x1060b8c448134614 0x21060b8c44813461 0xb0e7f0cc483f0677 0xdb0e7f0cc483f067

def z733 : W := mkw 0x1a82b66c241b3332 0x21a82b66c241b333 0x6f07f33c363f99f9 0x26f07f33c363f99f

def z734 : W := mkw 0x4109e05582c582d1 0x44109e05582c582d 0x7319f0ff8fc787ff 0xb7319f0ff8fc787f

def z735 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4cffffff80000003 0x44cffffff8000000

def z736 : W := mkw 0x4fdfefff11282820 0x84fdfefff1128282 0xeffffffff1f8780f 0xfeffffffff1f8780

def z737 : W := mkw 0x0060088048004404 0x0006008804800440 0xdfe00ff07e00ff8e 0xfdfe00ff07e00ff8

def z738 : W := mkw 0x4bc9eaf59168a861 0x84bc9eaf59168a86 0xb3e1f0f071f8f87c 0x8b3e1f0f071f8f87

def z739 : W := mkw 0x251d500013b60008 0x0251d500013b6000 0x20fff00001ff0001 0xd20fff00001ff000

def z740 : W := mkw 0x0434100059320000 0x0043410005932000 0xa0fff00049ff0005 0xda0fff00049ff000

def z741 : W := mkw 0x116b3c99cadee4e5 0x6116b3c99cadee4e 0xc3fe7c33c7f8e188 0x6c3fe7c33c7f8e18

def z742 : W := mkw 0x20201000fffefd6f 0x820201000fffefd6 0xb00000007ffffffc 0x0b00000007ffffff

def z743 : W := mkw 0x4ed66faa00000000 0x04ed66faa0000000 0x4ce67f0f80000002 0x44ce67f0f8000000

def z744 : W := mkw 0x255d5aa013b6550e 0x0255d5aa013b6550 0x701ffff001ffff83 0x0701ffff001ffff8

def z745 : W := mkw 0x0000000082c582d1 0x40000000082c582d 0x731800ff8fc787ff 0xb731800ff8fc787f

def z746 : W := mkw 0x1042adce8049ee75 0xa1042adce8049ee7 0x10000ccf80006672 0x010000ccf8000667

def z747 : W := mkw 0x4fdf6fbb00000000 0x04fdf6fbb0000000 0x0cfe7f0380000000 0x40cfe7f038000000

def z748 : W := mkw 0x3fdfeccc37ad663c 0x23fdfeccc37ad663 0x1f180ccc37c0667a 0x21f180ccc37c0667

def z749 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x631980ff8fc787f9 0xa631980ff8fc787f

def z750 : W := mkw 0x1042afee8049ff77 0xa1042afee8049ff7 0x50000fff8000fff2 0x050000fff8000fff

def z751 : W := mkw 0x20201000fff68049 0x020201000fff6804 0xb00000007fff807c 0x0b00000007fff807

def z752 : W := mkw 0x4fdfefff00010290 0x44fdfefff0001029 0x4fffffff80000783 0xf4fffffff8000078

def z753 : W := mkw 0x4f9f473b00000000 0x04f9f473b0000000 0x4fffff3f80000003 0xf4fffff3f8000000

def z754 : W := mkw 0x0f9d400000000000 0x00f9d40000000000 0x4ffff00f80000003 0xf4ffff00f8000000

def z755 : W := mkw 0x1be9baf56e975796 0x61be9baf56e97579 0x03e1f0f00e070780 0x803e1f0f00e07078

def z756 : W := mkw 0x2f9d4000b7e480c9 0x42f9d4000b7e480c 0x0f18000037c08188 0x20f18000037c0818

def z757 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xfce7ffcc483f6677 0xffce7ffcc483f667

def z758 : W := mkw 0x4f9fe55f00000000 0x04f9fe55f0000000 0x4fffff0f80000003 0xf4fffff0f8000000

def z759 : W := mkw 0x5062bfff481b7736 0x25062bfff481b773 0xf0e7ffffc83ffff7 0xdf0e7ffffc83ffff

def z760 : W := mkw 0x4042afff8049aaf1 0xc4042afff8049aaf 0x50000fff8000fff2 0x050000fff8000fff

def z761 : W := mkw 0x4fdfefff00005506 0x04fdfefff0000550 0x4fffffff80007803 0xf4fffffff8000780

def z762 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xffe00ffc7e00ffff 0xfffe00ffc7e00fff

def z763 : W := mkw 0x051f855f13ad2ab0 0xc051f855f13ad2ab 0x8f078ff07e3f7f80 0xc8f078ff07e3f7f8

def z764 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xacfff00079ff0005 0xdacfff00079ff000

def z765 : W := mkw 0x4ed6efee00000000 0x04ed6efee0000000 0x4cffffcf80000003 0xf4cffffcf8000000

def z766 : W := mkw 0x4f9d433393e488c1 0xc4f9d433393e488c 0x4f180333b7c09988 0x24f180333b7c0998

def z767 : W := mkw 0x4fdfefff02840000 0x04fdfefff0284000 0x4fffffff87c0000b 0xf4fffffff87c0000

def z768 : W := mkw 0x0ae01aa06c125506 0x00ae01aa06c12550 0xdfe67ff07e38ff8e 0xfdfe67ff07e38ff8

def z769 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xa3fff0004fff0005 0xda3fff0004fff000

def z770 : W := mkw 0x0ae01aa06c125506 0x00ae01aa06c12550 0xffe00ff07e3fff8e 0xfffe00ff07e3fff8

def z771 : W := mkw 0x4fdfefff00010210 0x04fdfefff0001021 0x6fffffff80070073 0xf6fffffff8007007

def z772 : W := mkw 0x10201000d97bee75 0xa10201000d97bee7 0xb000000049ff6674 0x0b000000049ff667

def z773 : W := mkw 0x0fdfecdd00000000 0x00fdfecdd0000000 0x4ffffcff80000003 0xf4ffffcff8000000

def z774 : W := mkw 0x2eb4d055fd7382d9 0x42eb4d055fd7382d 0xdce670fff03887f2 0x4dce670fff03887f

def z775 : W := mkw 0x4fdfefff24005506 0x04fdfefff2400550 0x5fffffffb600ff8b 0xf5fffffffb600ff8

def z776 : W := mkw 0x1ef63faa7d3a7d26 0xa1ef63faa7d3a7d2 0x8ce67f0070387800 0x48ce67f007038780

def z777 : W := mkw 0x2bab550aeedea869 0x82bab550aeedea86 0x53e1ff0f8e07f872 0x853e1ff0f8e07f87

def z778 : W := mkw 0x00400aa000005506 0x000400aa00000550 0xdf000ff07e00ff8e 0xfdf000ff07e00ff8

def z779 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xacfff00071ff000d 0x7acfff00071ff000

def z780 : W := mkw 0x20201000fffea869 0x820201000fffea86 0xa00000007fff007c 0x0a00000007fff007

def z781 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xa0e7fccc403f6073 0xda0e7fccc403f607

def z782 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0xdfffffffc0006007 0xfdfffffffc000600

def z783 : W := mkw 0x1062bccc6c1b6634 0x21062bccc6c1b663 0xb0e7fccc7e3f667f 0xdb0e7fccc7e3f667

def z784 : W := mkw 0x2be9daf56e97579e 0x42be9daf56e97579 0x03e1f0f00e070780 0x803e1f0f00e07078

def z785 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0x30e7fccc083f6673 0x830e7fccc083f667

def z786 : W := mkw 0x20201000eed782d9 0x420201000eed782d 0x300000000fc787fc 0x0300000000fc787f

def z787 : W := mkw 0x1062beec6c1b7736 0x21062beec6c1b773 0xf0e7fffc7e3fffff 0xdf0e7fffc7e3ffff

def z788 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xaffff00077ff0009 0x6affff00077ff000

def z789 : W := mkw 0x5042afff8049e6f5 0x65042afff8049e6f 0x50000fff8000e7f2 0x050000fff8000e7f

def z790 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xbce7ffcc783f7e77 0xdbce7ffcc783f7e7

def z791 : W := mkw 0x2f9d500013b60008 0x02f9d500013b6000 0x2ffff0000fff000d 0xf2ffff0000fff000

def z792 : W := mkw 0x1062bccc481b7736 0x21062bccc481b773 0xb0e7fccc483ffff7 0xdb0e7fccc483ffff

def z793 : W := mkw 0x0ac00aa024005506 0x00ac00aa02400550 0x5fe00ff03600ff8a 0xf5fe00ff03600ff8

def z794 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xbffff0007fff878d 0xfbffff0007fff878

def z795 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xa3fff0007fff000d 0x8a3fff0007fff000

def z796 : W := mkw 0x243410007fb60008 0x0243410007fb6000 0xacfff0007fff000d 0xfacfff0007fff000

def z797 : W := mkw 0x10201000cad7c6d5 0x610201000cad7c6d 0x300000000fc787fc 0x0300000000fc787f

def z798 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0e7fc0c483f6675 0x4b0e7fc0c483f667

def z799 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x0fffff0f80000001 0xf0fffff0f8000000

def z800 : W := mkw 0x0ef60faafd68fd67 0x80ef60faafd68fd6 0x23fe00ff8ff807f1 0x823fe00ff8ff807f

def z801 : W := mkw 0x4bc9eaf500000000 0x04bc9eaf50000000 0x43e1f0ff80000002 0x843e1f0ff8000000

def z802 : W := mkw 0x451fe55f00000000 0x0451fe55f0000000 0x00fff00f80000001 0xd00fff00f8000000

def z803 : W := mkw 0x1042accc8049e6f5 0x61042accc8049e6f 0x10000ccc0000e7f2 0x010000ccc0000e7f

def z804 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0x2ffff0000fff0001 0xf2ffff0000fff000

def z805 : W := mkw 0x0ac00aa000000000 0x00ac00aa00000000 0xdfe00ff07e00ff8e 0xfdfe00ff07e00ff8

def z806 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x631980ff8fc707f3 0xb631980ff8fc707f

def z807 : W := mkw 0x0000804480418251 0x0000080448041825 0x731980ff8fc787ff 0xb731980ff8fc787f

def z808 : W := mkw 0x0020100048130210 0x0002010004813021 0xb0e7f000483f0675 0xdb0e7f000483f067

def z809 : W := mkw 0x2ef65faa7d3a7d2e 0x82ef65faa7d3a7d2 0x8ce67f0070387800 0x48ce67f007038780

def z810 : W := mkw 0x00201000d97aa861 0x800201000d97aa86 0xb000000079fff87c 0x0b000000079fff87

def z811 : W := mkw 0x4bcbefff00000000 0x04bcbefff0000000 0x4fe1ffff80000002 0xf4fe1ffff8000000

def z812 : W := mkw 0x4fddebf700000000 0x04fddebf70000000 0x4ffff3f380000001 0xf4ffff3f38000000

def z813 : W := mkw 0x6f9d4333b7e480c9 0x46f9d4333b7e480c 0x4f180333b7c08188 0x24f180333b7c0818

def z814 : W := mkw 0x20201000fd7aa869 0x820201000fd7aa86 0xb000000071f8f87c 0x0b000000071f8f87

def z815 : W := mkw 0x212990557fb60008 0x0212990557fb6000 0xe31980ffffff000f 0xbe31980ffffff000

def z816 : W := mkw 0x5fbd5333481b6634 0x25fbd5333481b663 0xff180333c83f6674 0x2ff180333c83f667

def z817 : W := mkw 0x4fdfefff11200000 0x04fdfefff1120000 0xcffffffff0380003 0xfcffffffff038000

def z818 : W := mkw 0x455fefff00000000 0x0455fefff0000000 0x40ffffff80000003 0xd40ffffff8000000

def z819 : W := mkw 0x453fe55f6c005506 0x0453fe55f6c00550 0x901ff00ffe00ff8d 0x0901ff00ffe00ff8

def z820 : W := mkw 0x4ed66faa82c582d1 0x44ed66faa82c582d 0x3ce67f000fc787fc 0x43ce67f000fc787f

def z821 : W := mkw 0x0fdf4faa00000000 0x00fdf4faa0000000 0x4fffffff80000003 0xf4fffffff8000000

def z822 : W := mkw 0x2f9d500013b60008 0x02f9d500013b6000 0x23fff00001ff0001 0x823fff00001ff000

def z823 : W := mkw 0x6fdfefff13a40008 0x06fdfefff13a4000 0x4fffffff81c00003 0xf4fffffff81c0000

def z824 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x9fe00ff07e00ff8c 0xc9fe00ff07e00ff8

def z825 : W := mkw 0x2fbd50117fb60008 0x02fbd50117fb6000 0xeffff033ffff000d 0xfeffff033ffff000

def z826 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0x23fff0000fff000d 0xb23fff0000fff000

def z827 : W := mkw 0x1062bdce481b6e34 0xa1062bdce481b6e3 0xb0e7ffcc483f7e77 0xdb0e7ffcc483f7e7

def z828 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xf0e7fcfc483fe7f7 0xdf0e7fcfc483fe7f

def z829 : W := mkw 0x0042accc82c582d1 0x40042accc82c582d 0x30e7fccc0fc787ff 0xd30e7fccc0fc787f

def z830 : W := mkw 0x6062bfff7fb60008 0x06062bfff7fb6000 0xe0000fffffff000e 0x0e0000fffffff000

def z831 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x5fffffff8000f803 0xf5fffffff8000f80

def z832 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0xcffffffff0007803 0xfcffffffff000780

def z833 : W := mkw 0x0020100048120000 0x0002010004812000 0xa0fff00049ff000d 0xfa0fff00049ff000

def z834 : W := mkw 0x4fdf6faa00000000 0x04fdf6faa0000000 0x4fffff0f80000003 0xf4fffff0f8000000

def z835 : W := mkw 0x10201000cadfe6f5 0x610201000cadfe6f 0xb000000049ff6674 0x0b000000049ff667

def z836 : W := mkw 0x0fdfedce00000000 0x00fdfedce0000000 0x4fffffcf80000003 0xf4fffffcf8000000

def z837 : W := mkw 0x4f9fe77f00000000 0x04f9fe77f0000000 0x4ffff33f80000001 0xf4ffff33f8000000

def z838 : W := mkw 0x2f9d4102b7e48849 0x82f9d4102b7e4884 0x0f180003b7c00008 0x20f180003b7c0000

def z839 : W := mkw 0x4456afff00000000 0x04456afff0000000 0x4cffffff80000003 0xf4cffffff8000000

def z840 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xdf000ff07e00ff8e 0x2df000ff07e00ff8

def z841 : W := mkw 0x2f9d4322b7e4994b 0x82f9d4322b7e4994 0x4f180333b7c09988 0x24f180333b7c0998

def z842 : W := mkw 0x0f9f450a00000000 0x00f9f450a0000000 0x0ffff00f80000001 0xf0ffff00f8000000

def z843 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xfcffff0ff1f8f87f 0xffcffff0ff1f8f87

def z844 : W := mkw 0x4ed66faa00000000 0x04ed66faa0000000 0x4ffe7fff80000003 0xf4ffe7fff8000000

def z845 : W := mkw 0x4f9d433300000000 0x04f9d43330000000 0x4ffe733380000000 0x64ffe73338000000

def z846 : W := mkw 0x0042adce00000000 0x00042adce0000000 0x40e7ffcf80000003 0xd40e7ffcf8000000

def z847 : W := mkw 0x251fd55f93ffaaf9 0xc251fd55f93ffaaf 0x201ff00f81ff0071 0x0201ff00f81ff007

def z848 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x73fff0ff8fc787ff 0xf73fff0ff8fc787f

def z849 : W := mkw 0x2eb450007fb60008 0x02eb450007fb6000 0xace7f0007fff000d 0xdace7f0007fff000

def z850 : W := mkw 0x5062befd481b6634 0x25062befd481b663 0xb0e7fcfc483f6677 0xdb0e7fcfc483f667

def z851 : W := mkw 0x0042accc00000000 0x00042accc0000000 0x40fffccf80000003 0xf40fffccf8000000

def z852 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0fffccc49ff667f 0xfb0fffccc49ff667

def z853 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xa0e7fc0c483f6075 0xda0e7fc0c483f607

def z854 : W := mkw 0x1022b44c481b2230 0x21022b44c481b223 0xb0e7f0cc483f0677 0xdb0e7f0cc483f067

def z855 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xffe7fffc7e3fffff 0xfffe7fffc7e3ffff

def z856 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xec1e0f0ff1f87873 0x7ec1e0f0ff1f8787

def z857 : W := mkw 0x2fbd52207fb6110a 0x02fbd52207fb6110 0xfffff3f07fff9f8f 0xffffff3f07fff9f8

def z858 : W := mkw 0x4416650a9168a861 0x84416650a9168a86 0xfc1e7f0ff1f8f87f 0x7fc1e7f0ff1f8f87

def z859 : W := mkw 0x4bc9eaf500000000 0x04bc9eaf50000000 0x4ff9ffff80000003 0xf4ff9ffff8000000

def z860 : W := mkw 0x4bcbefff00000000 0x04bcbefff0000000 0x43f9ffff80000003 0xb43f9ffff8000000

def z861 : W := mkw 0x0062bccc48130210 0x00062bccc4813021 0xb0e7fccc483f0677 0xdb0e7fccc483f067

def z862 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4fe7ffff80000002 0xc4fe7ffff8000000

def z863 : W := mkw 0x10623c88481a6424 0x210623c88481a642 0xb0e7fc0c483f6077 0xdb0e7fc0c483f607

def z864 : W := mkw 0x0bcbaefd00000000 0x00bcbaefd0000000 0x4fffffff80000003 0xf4fffffff8000000

def z865 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xbffff0007ffff80d 0xfbffff0007ffff80

def z866 : W := mkw 0x10221408481b6634 0x210221408481b663 0xb0e7fc0c483f6677 0xdb0e7fc0c483f667

def z867 : W := mkw 0x4bcbeefd00000000 0x04bcbeefd0000000 0x43fffcff80000003 0xf43fffcff8000000

def z868 : W := mkw 0x10201000c85be6f5 0x610201000c85be6f 0xb0000000483fe7f4 0x0b0000000483fe7f

def z869 : W := mkw 0x2fbd50007fb6550e 0x02fbd50007fb6550 0xaffff0007fff078d 0xfaffff0007fff078

def z870 : W := mkw 0x4fdfefff02850290 0x44fdfefff0285029 0x7fffffff8e0707f7 0xf7fffffff8e0707f

def z871 : W := mkw 0x20201000fff680c9 0x420201000fff680c 0xa00000007fff818c 0x0a00000007fff818

def z872 : W := mkw 0x4fdfefff24001102 0x04fdfefff2400110 0x5fffffffbe009f8f 0xf5fffffffbe009f8

def z873 : W := mkw 0x0ed6afee00000000 0x00ed6afee0000000 0x4fffffff80000003 0xf4fffffff8000000

def z874 : W := mkw 0x0e96450a00000000 0x00e96450a0000000 0x4cfe7f0f80000003 0x74cfe7f0f8000000

def z875 : W := mkw 0x455feddf00000000 0x0455feddf0000000 0x00fffc0f80000001 0x400fffc0f8000000

def z876 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xeffff0f07fff000f 0xfeffff0f07fff000

def z877 : W := mkw 0x1042bccc001b2230 0x21042bccc001b223 0x20e7fc0c003f0071 0x420e7fc0c003f007

def z878 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xafffff007fff780d 0xfafffff007fff780

def z879 : W := mkw 0x455feddf00000000 0x0455feddf0000000 0x43fffcff80000003 0xf43fffcff8000000

def z880 : W := mkw 0x04562d8a00000000 0x004562d8a0000000 0x4cfe7f0f80000003 0x74cfe7f0f8000000

def z881 : W := mkw 0x253d50005bb60008 0x0253d50005bb6000 0xa0fff00041ff0001 0x4a0fff00041ff000

def z882 : W := mkw 0x4fddebf700000000 0x04fddebf70000000 0x4ff9fff380000002 0xf4ff9fff38000000

def z883 : W := mkw 0x0020100059320000 0x0002010005932000 0xa0e7f00079ff000d 0xda0e7f00079ff000

def z884 : W := mkw 0x1042acdd8049e6f5 0x61042acdd8049e6f 0x10000ccf80006672 0x010000ccf8000667

def z885 : W := mkw 0x2fbd52207fb6550e 0x02fbd52207fb6550 0xfffff3307fffff8d 0xffffff3307fffff8

def z886 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xeffff00fffff000f 0xfeffff00fffff000

def z887 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0xefffffffc0380007 0xfefffffffc038000

def z888 : W := mkw 0x2fbd52207fb6110a 0x02fbd52207fb6110 0xffffff307ffff98f 0xfffffff307ffff98

def z889 : W := mkw 0x4fdfefff11200000 0x04fdfefff1120000 0xfffffffff1f8f80f 0xffffffffff1f8f80

def z890 : W := mkw 0x1042aefd8049f7f7 0x61042aefd8049f7f 0x50000fff8000fff2 0x050000fff8000fff

def z891 : W := mkw 0x212910007fb60008 0x0212910007fb6000 0xa3fff0007fff000d 0xfa3fff0007fff000

def z892 : W := mkw 0x4ed66fbb00000000 0x04ed66fbb0000000 0x4ce67f3380000000 0x44ce67f338000000

def z893 : W := mkw 0x2fbd50117fb60088 0x42fbd50117fb6008 0xaffff0307fff018d 0xfaffff0307fff018

def z894 : W := mkw 0x4fdfefff00082020 0x04fdfefff0008202 0xcfffffffc0386003 0xfcfffffffc038600

def z895 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xcfe00ff07e00ff88 0xecfe00ff07e00ff8

def z896 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xaffff0007fff0001 0xcaffff0007fff000

def z897 : W := mkw 0x00221408481a2020 0x000221408481a202 0xa0e7f00c483f0075 0xda0e7f00c483f007

def z898 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xf0fffccfc83f6677 0xff0fffccfc83f667

def z899 : W := mkw 0x455feddf00000000 0x0455feddf0000000 0x4cffffcf80000003 0xf4cffffcf8000000

def z900 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0x30e7f0cc083f0677 0x930e7f0cc083f067

def z901 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xdc1e0f0ff1f8f87a 0x6dc1e0f0ff1f8f87

def z902 : W := mkw 0x4fdfefff02840000 0x04fdfefff0284000 0x7fffffff8fc7878f 0xf7fffffff8fc7878

def z903 : W := mkw 0x0416050a00000000 0x00416050a0000000 0x4cffff0f80000003 0xf4cffff0f8000000

def z904 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x231980ff8fc707fd 0xb231980ff8fc707f

def z905 : W := mkw 0x5062bfff481b6634 0x25062bfff481b663 0xf0000fffc83f6676 0x0f0000fffc83f667

def z906 : W := mkw 0x4ac2efff00000000 0x04ac2efff0000000 0x40e07fff80000002 0x040e07fff8000000

def z907 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0xf31980ffffc7ffff 0xbf31980ffffc7fff

def z908 : W := mkw 0x1062bcdd481b6634 0x21062bcdd481b663 0xf0e7fcffc83f6677 0xdf0e7fcffc83f667

def z909 : W := mkw 0x4f9fe55f00000000 0x04f9fe55f0000000 0x03fff00f80000001 0x803fff00f8000000

def z910 : W := mkw 0x4042addf00000000 0x04042addf0000000 0x00e7fccf80000003 0xd00e7fccf8000000

def z911 : W := mkw 0x6fdfefff26840008 0x06fdfefff2684000 0x4fffffff86000003 0xf4fffffff8600000

def z912 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0x20e7fccc083f0673 0xd20e7fccc083f067

def z913 : W := mkw 0x4fdfefff02850290 0x44fdfefff0285029 0x5fffffff8e07878f 0xf5fffffff8e07878

def z914 : W := mkw 0x1062bccc6c1b7736 0x21062bccc6c1b773 0xfce7ffcc7e3fffff 0xffce7ffcc7e3ffff

def z915 : W := mkw 0x4fdfefff02840080 0x44fdfefff0284008 0x4fffffff86000183 0xf4fffffff8600018

def z916 : W := mkw 0x4fdfefff00082020 0x04fdfefff0008202 0xfffffffff038f87f 0xffffffffff038f87

def z917 : W := mkw 0x2fbd52207fb60008 0x02fbd52207fb6000 0xeffff3307fff000d 0xfeffff3307fff000

def z918 : W := mkw 0x253d50005bb60008 0x0253d50005bb6000 0x20fff00009ff0001 0x820fff00009ff000

def z919 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x43ffffff80000003 0x843ffffff8000000

def z920 : W := mkw 0x0fbd500059320000 0x00fbd50005932000 0xaffff00079ff000d 0xfaffff00079ff000

def z921 : W := mkw 0x4fdfeddf00000000 0x04fdfeddf0000000 0x0ffffccf80000003 0xf0ffffccf8000000

def z922 : W := mkw 0x10201000fd7bff77 0xa10201000fd7bff7 0xb00000007ffffffc 0x0b00000007ffffff

def z923 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xeffff3007fff980d 0xfeffff3007fff980

def z924 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0xff1980ffffc787ff 0xfff1980ffffc787f

def z925 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x6fffffff88070007 0xf6fffffff8807000

def z926 : W := mkw 0x0eb410007d320000 0x00eb410007d32000 0xaffff0007fff000d 0xfaffff0007fff000

def z927 : W := mkw 0x30201000ffffee7d 0xa30201000ffffee7 0xb00000007ffffe7c 0x0b00000007ffffe7

def z928 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0x20fff00001ff0001 0x020fff00001ff000

def z929 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4cffff0f80000003 0x74cffff0f8000000

def z930 : W := mkw 0x006098c448134614 0x0006098c44813461 0xb0e7fccc483f6677 0xdb0e7fccc483f667

def z931 : W := mkw 0x4fdfefff11200000 0x04fdfefff1120000 0x6fffffff81f80003 0xf6fffffff81f8000

def z932 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0xf31f80ffcfff87ff 0xff31f80ffcfff87f

def z933 : W := mkw 0x0f9dc05500000000 0x00f9dc0550000000 0x0ffff00f80000001 0xf0ffff00f8000000

def z934 : W := mkw 0x2eb450007d320008 0x02eb450007d32000 0xacfff00079ff000d 0xfacfff00079ff000

def z935 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xac1e0f0ff1f8787d 0x7ac1e0f0ff1f8787

def z936 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4fffffffb000980b 0xf4fffffffb000980

def z937 : W := mkw 0x0456adce00000000 0x00456adce0000000 0x00fffccf80000003 0xd00fffccf8000000

def z938 : W := mkw 0x151fb55f93ffaaf1 0xe151fb55f93ffaaf 0x201ff00f81ff0071 0x0201ff00f81ff007

def z939 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x7f1983ffbfc79fff 0xb7f1983ffbfc79ff

def z940 : W := mkw 0x4ed6efff00000000 0x04ed6efff0000000 0x4cfe7fff80000003 0x74cfe7fff8000000

def z941 : W := mkw 0x2fbd50007fb6550e 0x02fbd50007fb6550 0xaffff0007fff780d 0xfaffff0007fff780

def z942 : W := mkw 0x6fbd51137fb60008 0x06fbd51137fb6000 0xaffff003ffff000d 0xfaffff003ffff000

def z943 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0x2ffff0003fff0009 0xa2ffff0003fff000

def z944 : W := mkw 0x2ba950007fb60008 0x02ba950007fb6000 0xa3e7f0007fff000d 0xda3e7f0007fff000

def z945 : W := mkw 0x0f9fc55f00000000 0x00f9fc55f0000000 0x4fffffff80000003 0xf4fffffff8000000

def z946 : W := mkw 0x4bcbefff00000000 0x04bcbefff0000000 0x03e1f0ff80000000 0x803e1f0ff8000000

def z947 : W := mkw 0x4fddebf700000000 0x04fddebf70000000 0x4ff9f3ff80000003 0xb4ff9f3ff8000000

def z948 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x731980ff8fc787f3 0x8731980ff8fc787f

def z949 : W := mkw 0x4f9d433300000000 0x04f9d43330000000 0x4ff9f33380000000 0xa4ff9f3338000000

def z950 : W := mkw 0x0020100048120000 0x0002010004812000 0xb0e7f00c483f0077 0xdb0e7f00c483f007

def z951 : W := mkw 0x4fdfefff00010210 0x04fdfefff0001021 0x7fffffff8e0787ff 0xf7fffffff8e0787f

def z952 : W := mkw 0x4f9fe55f00000000 0x04f9fe55f0000000 0x4ffff0ff80000003 0xf4ffff0ff8000000

def z953 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xffe18ff07e07ff8f 0xfffe18ff07e07ff8

def z954 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x03fffcff80000003 0xd03fffcff8000000

def z955 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xdfe7fff07e00ff8f 0xfdfe7fff07e00ff8

def z956 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x43fff0ff80000003 0xb43fff0ff8000000

def z957 : W := mkw 0x4fddeaf500000000 0x04fddeaf50000000 0x4ffff0ff80000003 0xf4ffff0ff8000000

def z958 : W := mkw 0x0f9d401100000000 0x00f9d40110000000 0x4ffff03380000001 0xf4ffff0338000000

def z959 : W := mkw 0x4ed66faa00000000 0x04ed66faa0000000 0x0cfe7f0f80000001 0x40cfe7f0f8000000

def z960 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x531980ff8fc787fa 0xa531980ff8fc787f

def z961 : W := mkw 0x0062bccc481a2020 0x00062bccc481a202 0xb0e7fccc483f6077 0xdb0e7fccc483f607

def z962 : W := mkw 0x1062bdce481b6634 0x21062bdce481b663 0xf0e7ffcfc83f6677 0xdf0e7ffcfc83f667

def z963 : W := mkw 0x00201000cad782d1 0x400201000cad782d 0xb00000004fff87fc 0x0b00000004fff87f

def z964 : W := mkw 0x4fdfefff00082020 0x04fdfefff0008202 0x6fffffff80380073 0xf6fffffff8038007

def z965 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xaffff0f07fff078d 0xfaffff0f07fff078

def z966 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xf3e7fcfc483f6677 0xff3e7fcfc483f667

def z967 : W := mkw 0x000000009168a861 0x8000000009168a86 0xfc180f0ff1f8f87f 0x7fc180f0ff1f8f87

def z968 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xf0e7fccc483fe67f 0xff0e7fccc483fe67

def z969 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xbffff00c7fff007f 0xfbffff00c7fff007

def z970 : W := mkw 0x2f9d4011b7e480c9 0x42f9d4011b7e480c 0x0f180003b7c00008 0x20f180003b7c0000

def z971 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x0cffffcf80000003 0xd0cffffcf8000000

def z972 : W := mkw 0x4fdf6fbb00000000 0x04fdf6fbb0000000 0x4fffff3380000001 0xf4fffff338000000

def z973 : W := mkw 0x6fdfefff37a40008 0x06fdfefff37a4000 0xeffffffff7f8000f 0xfeffffffff7f8000

def z974 : W := mkw 0x4fdfefff00092230 0x04fdfefff0009223 0xffffffffc83f6677 0xfffffffffc83f667

def z975 : W := mkw 0x2f9d4231b7e491cb 0x42f9d4231b7e491c 0x4f180333b7c09988 0x24f180333b7c0998

def z976 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x731800ff8fc787fe 0x2731800ff8fc787f

def z977 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x7fffffff80000077 0xf7fffffff8000007

def z978 : W := mkw 0x4fdfefff00004404 0x04fdfefff0000440 0x5fffffff80006603 0xf5fffffff8000660

def z979 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xfff80ff07fc0ff8f 0xffff80ff07fc0ff8

def z980 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4fffffff8e00000f 0xf4fffffff8e00000

def z981 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0e7f0cc483f6675 0x8b0e7f0cc483f667

def z982 : W := mkw 0x4fdfefff00082020 0x04fdfefff0008202 0x5fffffff80006073 0xf5fffffff8000607

def z983 : W := mkw 0x10201000eedff7f7 0x610201000eedff7f 0xb00000007ffffffc 0x0b00000007ffffff

def z984 : W := mkw 0x6fbd52317fb60008 0x06fbd52317fb6000 0xaffff0307fff000d 0xfaffff0307fff000

def z985 : W := mkw 0x0b89c05500000000 0x00b89c0550000000 0x43f9f0ff80000003 0xb43f9f0ff8000000

def z986 : W := mkw 0x002000006c005506 0x0002000006c00550 0xdf000ff07e00ff8e 0xfdf000ff07e00ff8

def z987 : W := mkw 0x2f9d500013b60008 0x02f9d500013b6000 0xaffff00071ff000d 0xfaffff00071ff000

def z988 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xa0e7fccc483f6671 0xca0e7fccc483f667

def z989 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0xdffffffffe00ff8f 0xfdffffffffe00ff8

def z990 : W := mkw 0x4fdfefff00010210 0x04fdfefff0001021 0x4fffffff88070603 0xf4fffffff8807060

def z991 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4fffffff8600818b 0xf4fffffff8600818

def z992 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xaffff00071ff0001 0xfaffff00071ff000

def z993 : W := mkw 0x0042acdd00000000 0x00042acdd0000000 0x40e7fcff80000003 0xd40e7fcff8000000

def z994 : W := mkw 0x4fdfefff00001102 0x04fdfefff0000110 0x4fffffff80009983 0xf4fffffff8000998

def z995 : W := mkw 0x10201000d97aec65 0xa10201000d97aec6 0xb000000071f8f87c 0x0b000000071f8f87

def z996 : W := mkw 0x1022b44c481b6634 0x21022b44c481b663 0xb0e7f00c483f6675 0xdb0e7f00c483f667

def z997 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb3e7fcfc4e3f67f7 0xdb3e7fcfc4e3f67f

def z998 : W := mkw 0x4fdf6fbb00000000 0x04fdf6fbb0000000 0x4ffe7f3f80000003 0x74ffe7f3f8000000

def z999 : W := mkw 0x4bc9eaf500000000 0x04bc9eaf50000000 0x03f9f0ff80000001 0x803f9f0ff8000000

def z1000 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4ffffff380000000 0xe4ffffff38000000

def z1001 : W := mkw 0x0022944c481b2230 0x00022944c481b223 0xb0e7fccc483f6677 0xdb0e7fccc483f667

def z1002 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0e7fccc4e3fe7ff 0xdb0e7fccc4e3fe7f

def z1003 : W := mkw 0x5fdfefff00086424 0x25fdfefff0008642 0x4fffffff80006003 0xf4fffffff8000600

def z1004 : W := mkw 0x2fbd51027fb60008 0x02fbd51027fb6000 0xeffff303ffff000d 0xfeffff303ffff000

def z1005 : W := mkw 0x10201000481b2230 0x210201000481b223 0xa0e7f000483f0075 0xda0e7f000483f007

def z1006 : W := mkw 0x6fdfefff37a40008 0x06fdfefff37a4000 0x6fffffffbfc7000f 0xf6fffffffbfc7000

def z1007 : W := mkw 0x0f9d410200000000 0x00f9d41020000000 0x4ffff30380000001 0xf4ffff3038000000

def z1008 : W := mkw 0x2aa010007fb60008 0x02aa010007fb6000 0xafe7f0007fff000d 0xfafe7f0007fff000

def z1009 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x5fffffff8000800f 0xf5fffffff8000800

def z1010 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x6fffffff81c0000f 0xf6fffffff81c0000

def z1011 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0xcffffffff000000f 0xfcffffffff000000

def z1012 : W := mkw 0x4ed66faa00000000 0x04ed66faa0000000 0x4cfe7f0380000000 0x64cfe7f038000000

def z1013 : W := mkw 0x0414000091608041 0x0041400009160804 0xfc1e0f0ff1f8f87f 0x7fc1e0f0ff1f8f87

def z1014 : W := mkw 0x6fbd53337fb6110a 0x06fbd53337fb6110 0xeffff333ffff998d 0xfeffff333ffff998

def z1015 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xacfff0007fff000d 0x4acfff0007fff000

def z1016 : W := mkw 0x5062bfee481b6634 0x25062bfee481b663 0xb0e7ffcc483f6677 0xdb0e7ffcc483f667

def z1017 : W := mkw 0x00201000481a2020 0x000201000481a202 0xb0e7f000483f6075 0xdb0e7f000483f607

def z1018 : W := mkw 0x4fdfefff02840000 0x04fdfefff0284000 0x4fffffff8e070003 0xf4fffffff8e07000

def z1019 : W := mkw 0x4fddebf700000000 0x04fddebf70000000 0x03f9f0f380000000 0x803f9f0f38000000

def z1020 : W := mkw 0x2fbd51027fb60808 0x82fbd51027fb6080 0xaffff3007fff180d 0xfaffff3007fff180

def z1021 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xeffff0307fff818d 0xfeffff0307fff818

def z1022 : W := mkw 0x0fddcaf500000000 0x00fddcaf50000000 0x4fffffff80000003 0xf4fffffff8000000

def z1023 : W := mkw 0x4fdfefff02850290 0x44fdfefff0285029 0x6fffffff8fc7078f 0xf6fffffff8fc7078

def z1024 : W := mkw 0x2f9d4000b7e48849 0x82f9d4000b7e4884 0x0f18000037c09808 0x20f18000037c0980

def z1025 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0x20e7f00c003f0071 0x020e7f00c003f007

def z1026 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4fffff3f80000001 0x64fffff3f8000000

def z1027 : W := mkw 0x0f9d400082c582d1 0x40f9d400082c582d 0x3ffff0000fc787fd 0xf3ffff0000fc787f

def z1028 : W := mkw 0x0ae01aa06c125506 0x00ae01aa06c12550 0xdfe1fff07e07ff8e 0xfdfe1fff07e07ff8

def z1029 : W := mkw 0x0ac00aa024005506 0x00ac00aa02400550 0xdf000ff07600ff8e 0x7df000ff07600ff8

def z1030 : W := mkw 0x0109805500000000 0x0010980550000000 0x43fff0ff80000003 0xf43fff0ff8000000

def z1031 : W := mkw 0x4fdfefff00010210 0x04fdfefff0001021 0x5fffffff80000673 0xf5fffffff8000067

def z1032 : W := mkw 0x1062bccc6c1b7736 0x21062bccc6c1b773 0xb0e7fccc4e3f67f7 0xdb0e7fccc4e3f67f

def z1033 : W := mkw 0x4bcbefff00000000 0x04bcbefff0000000 0x43e7ffff80000003 0xd43e7ffff8000000

def z1034 : W := mkw 0x2fbd50007fb6550e 0x02fbd50007fb6550 0xffffff007fffff8f 0xfffffff007fffff8

def z1035 : W := mkw 0x4fdfefff11282020 0x04fdfefff1128202 0xfffffffff1f8607f 0xffffffffff1f8607

def z1036 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0e7fcc0483f6674 0xcb0e7fcc0483f667

def z1037 : W := mkw 0x20201000ffffaaf9 0xc20201000ffffaaf 0xb00000007ffffffc 0x0b00000007ffffff

def z1038 : W := mkw 0x012910004a960000 0x0012910004a96000 0xa0fff00049ff0005 0xda0fff00049ff000

def z1039 : W := mkw 0x455feddf00000000 0x0455feddf0000000 0x00fff0cf80000001 0x800fff0cf8000000

def z1040 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0x90e7fccc483f6672 0xc90e7fccc483f667

def z1041 : W := mkw 0x4bc9eaf582c582d1 0x44bc9eaf582c582d 0x33e1f0f00fc787fc 0x833e1f0f00fc787f

def z1042 : W := mkw 0x2f9d500013b60008 0x02f9d500013b6000 0x2cfff00001ff0001 0x42cfff00001ff000

def z1043 : W := mkw 0x4fdfefff11282820 0x84fdfefff1128282 0xfffffffff0387877 0xffffffffff038787

def z1044 : W := mkw 0x4fdfefff24001102 0x04fdfefff2400110 0xdffffffff600f98f 0xfdffffffff600f98

def z1045 : W := mkw 0x5fdfefff00096634 0x25fdfefff0009663 0xffffffffc0386677 0xfffffffffc038667

def z1046 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xff1e0f0ffff8f87f 0xfff1e0f0ffff8f87

def z1047 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x331980ff8fc787fd 0x8331980ff8fc787f

def z1048 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0e7fc0c403f6077 0x5b0e7fc0c403f607

def z1049 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0x5fe00ff03e00ff8a 0xa5fe00ff03e00ff8

def z1050 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x00fff00f80000001 0x000fff00f8000000

def z1051 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xdfe00ff07e00ff82 0xcdfe00ff07e00ff8

def z1052 : W := mkw 0x4f9dc37700000000 0x04f9dc3770000000 0x4ffff3ff80000003 0xf4ffff3ff8000000

def z1053 : W := mkw 0x4fdfefff11200000 0x04fdfefff1120000 0x4fffffffb1c0000b 0xf4fffffffb1c0000

def z1054 : W := mkw 0x4ac2afff00000000 0x04ac2afff0000000 0x4fe7ffff80000003 0xf4fe7ffff8000000

def z1055 : W := mkw 0x4fdfefff02840000 0x04fdfefff0284000 0x6fffffff81c70003 0xf6fffffff81c7000

def z1056 : W := mkw 0x4bc9eaf500000000 0x04bc9eaf50000000 0x43f9f0f380000000 0xa43f9f0f38000000

def z1057 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xbce7fccc783f667f 0xfbce7fccc783f667

def z1058 : W := mkw 0x4f9d411300000000 0x04f9d41130000000 0x0ffff00380000001 0xf0ffff0038000000

def z1059 : W := mkw 0x30201000ffffe6fd 0x630201000ffffe6f 0xb00000007fffe7fc 0x0b00000007fffe7f

def z1060 : W := mkw 0x1042bccc001b2230 0x21042bccc001b223 0xb0e7fccc403f6077 0xdb0e7fccc403f607

def z1061 : W := mkw 0x1062beec481b7736 0x21062beec481b773 0xfce7fffc783fffff 0xffce7fffc783ffff

def z1062 : W := mkw 0x10601880481b6634 0x210601880481b663 0xb0e7fcc0483f6677 0xdb0e7fcc0483f667

def z1063 : W := mkw 0x4fdfefff11200800 0x84fdfefff1120080 0x4fffffffb0001803 0xf4fffffffb000180

def z1064 : W := mkw 0x4fdfefff00005506 0x04fdfefff0000550 0x5fffffff8e00ff8f 0xf5fffffff8e00ff8

def z1065 : W := mkw 0x1022b44c481b2230 0x21022b44c481b223 0xb0e7fc0c483f6077 0xdb0e7fc0c483f607

def z1066 : W := mkw 0x5fdfefff00014614 0x25fdfefff0001461 0x4fffffff80000603 0xf4fffffff8000060

def z1067 : W := mkw 0x1042bccc001b2230 0x21042bccc001b223 0x20e7f0cc003f0071 0x820e7f0cc003f007

def z1068 : W := mkw 0x10201000dbffeef5 0xe10201000dbffeef 0xb00000007ffffffc 0x0b00000007ffffff

def z1069 : W := mkw 0x10623c88481b6634 0x210623c88481b663 0xb0e7fc00483f6675 0xdb0e7fc00483f667

def z1070 : W := mkw 0x5fdfefff00092230 0x25fdfefff0009223 0x4fffffff80000073 0xf4fffffff8000007

def z1071 : W := mkw 0x4fdfefff02850290 0x44fdfefff0285029 0x4fffffff80070003 0xf4fffffff8007000

def z1072 : W := mkw 0x2fbd52207fb6110a 0x02fbd52207fb6110 0xaffff3007fff180d 0xfaffff3007fff180

def z1073 : W := mkw 0x1062beec481b7736 0x21062beec481b773 0xb0e7ffcc483f7e77 0xdb0e7ffcc483f7e7

def z1074 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x0fffffff80000001 0xc0fffffff8000000

def z1075 : W := mkw 0x1ae03aa06c125506 0x21ae03aa06c12550 0xdfe07ff07e00ff8e 0xfdfe07ff07e00ff8

def z1076 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xfc1e0fcff9f8fe7f 0xffc1e0fcff9f8fe7

def z1077 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x5fffffff88000607 0xf5fffffff8800060

def z1078 : W := mkw 0x4f9fe55f00000000 0x04f9fe55f0000000 0x0cfff00f80000001 0x40cfff00f8000000

def z1079 : W := mkw 0x1042accc8049ee75 0xa1042accc8049ee7 0x10000ccc0000fe72 0x010000ccc0000fe7

def z1080 : W := mkw 0x1062bcdd481b66b4 0x61062bcdd481b66b 0xb0e7fcfc483f67f7 0xdb0e7fcfc483f67f

def z1081 : W := mkw 0x6fdfefff37a4110a 0x06fdfefff37a4110 0x4fffffffb7c0998b 0xf4fffffffb7c0998

def z1082 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0x8ffff0007fff0008 0xe8ffff0007fff000

def z1083 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xff1e0ffff1f8f87f 0xfff1e0ffff1f8f87

def z1084 : W := mkw 0x4fdfefff11282820 0x84fdfefff1128282 0xdffffffff038f80f 0xfdffffffff038f80

def z1085 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x7f198fff8fc787ff 0xf7f198fff8fc787f

def z1086 : W := mkw 0x4fdfefff13a40000 0x04fdfefff13a4000 0xefffffffffff000f 0xfefffffffffff000

def z1087 : W := mkw 0x5fdfefff00096634 0x25fdfefff0009663 0x7fffffff88076677 0xf7fffffff8807667

def z1088 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xff1e0f3ff7f8f9ff 0x7ff1e0f3ff7f8f9f

def z1089 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x5fffffff80008783 0xf5fffffff8000878

def z1090 : W := mkw 0x0ac00aa024005506 0x00ac00aa02400550 0x5f000ff03e00ff8e 0xb5f000ff03e00ff8

def z1091 : W := mkw 0x253d50005bb60008 0x0253d50005bb6000 0xacfff00079ff000d 0xfacfff00079ff000

def z1092 : W := mkw 0x1002b44c001b2230 0x21002b44c001b223 0x20e7f00c003f0071 0xd20e7f00c003f007

def z1093 : W := mkw 0x1042accc8049e675 0x21042accc8049e67 0x50000ccf8000e672 0x050000ccf8000e67

def z1094 : W := mkw 0x4fdfefff24001102 0x04fdfefff2400110 0x4fffffff86000183 0xf4fffffff8600018

def z1095 : W := mkw 0x20201000fff7d7df 0x420201000fff7d7d 0xb00000007ffffffc 0x0b00000007ffffff

def z1096 : W := mkw 0x253d50005bb60008 0x0253d50005bb6000 0xa3fff0004fff000d 0xfa3fff0004fff000

def z1097 : W := mkw 0x2ae05aa06c12550e 0x02ae05aa06c12550 0xdfe07ff07e00ff8e 0xfdfe07ff07e00ff8

def z1098 : W := mkw 0x451fe55f93edaaf1 0xc451fe55f93edaaf 0x201ff00f81ff0071 0x0201ff00f81ff007

def z1099 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xfc1e0f0ff1f8f873 0x4fc1e0f0ff1f8f87

def z1100 : W := mkw 0x4fdf6fbb00000000 0x04fdf6fbb0000000 0x4ffe7ff380000002 0xf4ffe7ff38000000

def z1101 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0x331980ff8fc707f7 0x9331980ff8fc707f

def z1102 : W := mkw 0x4ae06aa06c005506 0x04ae06aa06c00550 0xdfe07ff07e00ff8e 0xfdfe07ff07e00ff8

def z1103 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xfc1f8f0ff9fff87f 0xffc1f8f0ff9fff87

def z1104 : W := mkw 0x1062beec481b6634 0x21062beec481b663 0xf0e7fffc483f6677 0xdf0e7fffc483f667

def z1105 : W := mkw 0x1042addf8049eef5 0xe1042addf8049eef 0x50000fff8000fff2 0x050000fff8000fff

def z1106 : W := mkw 0x0042accc9168a861 0x80042accc9168a86 0xb0e7fccc71f8f87f 0xdb0e7fccc71f8f87

def z1107 : W := mkw 0x6fbd53337fb60008 0x06fbd53337fb6000 0xef180333ffff000c 0x2ef180333ffff000

def z1108 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xa0e7f0cc483f0675 0xda0e7f0cc483f067

def z1109 : W := mkw 0x4fdfefff00005506 0x04fdfefff0000550 0xdffffffff000ff8f 0xfdffffffff000ff8

def z1110 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xbffff0c07fff060f 0xfbffff0c07fff060

def z1111 : W := mkw 0x000204088048a061 0x0000204088048a06 0xfc1e0f0ff1f8f87f 0x7fc1e0f0ff1f8f87

def z1112 : W := mkw 0x414bafff00000000 0x0414bafff0000000 0x43ffffff80000003 0xf43ffffff8000000

def z1113 : W := mkw 0x4ed6efff00000000 0x04ed6efff0000000 0x4ce7ffff80000003 0xd4ce7ffff8000000

def z1114 : W := mkw 0x00621c88481a6424 0x000621c88481a642 0xb0e7fccc483f6677 0xdb0e7fccc483f667

def z1115 : W := mkw 0x202010005bb60008 0x0202010005bb6000 0xa0e7f00049ff0005 0xda0e7f00049ff000

def z1116 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x0ffff0ff80000001 0xf0ffff0ff8000000

def z1117 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xfc1e0ffff1f8ffff 0x7fc1e0ffff1f8fff

def z1118 : W := mkw 0x4bc9ebf700000000 0x04bc9ebf70000000 0x43e1f3f380000000 0x843e1f3f38000000

def z1119 : W := mkw 0x1062bccc6c1b7736 0x21062bccc6c1b773 0xf3e7fcfc7e3fffff 0xff3e7fcfc7e3ffff

def z1120 : W := mkw 0x2f9d500037b60008 0x02f9d500037b6000 0x2ffff00037ff0009 0xf2ffff00037ff000

def z1121 : W := mkw 0x10201000c85be675 0x210201000c85be67 0xb000000049ffe67c 0x0b000000049ffe67

def z1122 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xfffffff07fffff8f 0xffffffff07fffff8

def z1123 : W := mkw 0x0aa000006c000000 0x00aa000006c00000 0xdfe00ff07e00ff8e 0xfdfe00ff07e00ff8

def z1124 : W := mkw 0x5042afff8049ee75 0xa5042afff8049ee7 0x50000fff8000fe72 0x050000fff8000fe7

def z1125 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xdfe00ff07600ff8a 0x6dfe00ff07600ff8

def z1126 : W := mkw 0x10209044481b6634 0x210209044481b663 0xb0e7f0cc483f6677 0xdb0e7f0cc483f667

def z1127 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb0e7fccc783ffe7f 0xdb0e7fccc783ffe7

def z1128 : W := mkw 0x20201000fff782d9 0x420201000fff782d 0xa00000007fff007c 0x0a00000007fff007

def z1129 : W := mkw 0x0f9d40009168a861 0x80f9d40009168a86 0xbffff00071f8f87d 0xfbffff00071f8f87

def z1130 : W := mkw 0x1022b44c481b2230 0x21022b44c481b223 0xa0e7f00c403f0071 0x4a0e7f00c403f007

def z1131 : W := mkw 0x0a80022024001102 0x00a8002202400110 0xdf000ff07e00ff8e 0xfdf000ff07e00ff8

def z1132 : W := mkw 0x4fdfefff11282820 0x84fdfefff1128282 0x4fffffff80380003 0xf4fffffff8038000

def z1133 : W := mkw 0x2fbd50007fb6440c 0x02fbd50007fb6440 0xbffff0007fff660d 0xfbffff0007fff660

def z1134 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xbffffc007fff600f 0xfbffffc007fff600

def z1135 : W := mkw 0x6f9d4333b7e48849 0x86f9d4333b7e4884 0x4f180333b7c09808 0x24f180333b7c0980

def z1136 : W := mkw 0x2fbd50005bb60008 0x02fbd50005bb6000 0xaffff00049ff0005 0xfaffff00049ff000

def z1137 : W := mkw 0x4042afff00000000 0x04042afff0000000 0x40e1ffff80000002 0x840e1ffff8000000

def z1138 : W := mkw 0x0fbd50004a960000 0x00fbd50004a96000 0xaffff0004fff000d 0xfaffff0004fff000

def z1139 : W := mkw 0x10201000c85bee75 0xa10201000c85bee7 0xb0000000483ffe74 0x0b0000000483ffe7

def z1140 : W := mkw 0x0042accc00092230 0x00042accc0009223 0xb0e7fccc483f6677 0xdb0e7fccc483f667

def z1141 : W := mkw 0x0109000082c48041 0x00109000082c4804 0x731980ff8fc787ff 0xb731980ff8fc787f

def z1142 : W := mkw 0x4fdfefff00082820 0x84fdfefff0008282 0x4fffffff80007803 0xf4fffffff8000780

def z1143 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xdff80ffffe00ff8f 0xfdff80ffffe00ff8

def z1144 : W := mkw 0x4042afff00000000 0x04042afff0000000 0x40e67fff80000002 0x440e67fff8000000

def z1145 : W := mkw 0x4fdfefff00005506 0x04fdfefff0000550 0x4fffffff80000783 0xf4fffffff8000078

def z1146 : W := mkw 0x1042bccc001b6634 0x21042bccc001b663 0x30e7fccc003f6673 0xd30e7fccc003f667

def z1147 : W := mkw 0x5062bddf481b6634 0x25062bddf481b663 0xb0e7fccfc83f6677 0xdb0e7fccfc83f667

def z1148 : W := mkw 0x1062bccc6c1b7736 0x21062bccc6c1b773 0xb0e7fccc783f7e77 0xdb0e7fccc783f7e7

def z1149 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xb3e7fccc4e3f667f 0xfb3e7fccc4e3f667

def z1150 : W := mkw 0x0ae00aa06c005506 0x00ae00aa06c00550 0xffe60ff07e38ff8f 0xfffe60ff07e38ff8

def z1151 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4ff9ffff80000002 0xa4ff9ffff8000000

def z1152 : W := mkw 0x4fdfefff24000000 0x04fdfefff2400000 0x4fffffffb600000b 0xf4fffffffb600000

def z1153 : W := mkw 0x014bacdd00000000 0x0014bacdd0000000 0x00fffccf80000003 0xd00fffccf8000000

def z1154 : W := mkw 0x4fdfefff24001102 0x04fdfefff2400110 0x4fffffffb0001803 0xf4fffffffb000180

def z1155 : W := mkw 0x1062beec481b7736 0x21062beec481b773 0xf3e7fffc4e3fffff 0xff3e7fffc4e3ffff

def z1156 : W := mkw 0x6fbd53227fb60008 0x06fbd53227fb6000 0xaffff3007fff000d 0xfaffff3007fff000

def z1157 : W := mkw 0x5fdfefff00097736 0x25fdfefff0009773 0x5fffffff8000fff3 0xf5fffffff8000fff

def z1158 : W := mkw 0x1062bccc481b6634 0x21062bccc481b663 0xf0e7ffcc483ffe77 0xdf0e7ffcc483ffe7

def z1159 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xafe7f0007fff000c 0xcafe7f0007fff000

def z1160 : W := mkw 0x2436150a7fb60008 0x02436150a7fb6000 0xec1e0f0fffff000f 0x7ec1e0f0fffff000

def z1161 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xfc180f0ff1f8f87e 0x2fc180f0ff1f8f87

def z1162 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4ffe7fff80000002 0x64ffe7fff8000000

def z1163 : W := mkw 0x20201000fff68849 0x820201000fff6884 0xa00000007fff980c 0x0a00000007fff980

def z1164 : W := mkw 0x1062bccc481b2230 0x21062bccc481b223 0xa0e7fccc483f0077 0xda0e7fccc483f007

def z1165 : W := mkw 0x11299055481b6634 0x211299055481b663 0xf31980ffc83f6677 0xbf31980ffc83f667

def z1166 : W := mkw 0x0109805582c582d1 0x40109805582c582d 0xf3198cffcfc7e7ff 0xff3198cffcfc7e7f

def z1167 : W := mkw 0x4ed66faa9168a861 0x84ed66faa9168a86 0xbce67f0071f8f87c 0x4bce67f0071f8f87

def z1168 : W := mkw 0x2fbd50007fb60008 0x02fbd50007fb6000 0xfffff0007fff800f 0xffffff0007fff800

def z1169 : W := mkw 0x2f9d4000b7e48049 0x02f9d4000b7e4804 0x4f180003b7c08008 0x24f180003b7c0800

def z1170 : W := mkw 0x4fdfefff00000000 0x04fdfefff0000000 0x4fffffff8e000783 0xf4fffffff8e00078

def z1171 : W := mkw 0x0f9d400013a40000 0x00f9d400013a4000 0xaffff0007fff000d 0xfaffff0007fff000

def z1172 : W := mkw 0x053d10005bb60000 0x0053d10005bb6000 0xaffff0007fff000d 0xfaffff0007fff000

def z1173 : W := mkw 0x0416050a9168a861 0x80416050a9168a86 0xbc1e0f0ff1f8f87d 0x4bc1e0f0ff1f8f87

def z1174 : W := mkw 0x2fbd52207fb6110a 0x02fbd52207fb6110 0xaffff0307fff018d 0xfaffff0307fff018

def z1175 : W := mkw 0x1436150a481b6634 0x21436150a481b663 0xfc1e0f0fc83f6677 0x7fc1e0f0fc83f667

def z1176 : W := mkw 0x4ed6efff00000000 0x04ed6efff0000000 0x0ce67f0f80000000 0x40ce67f0f8000000

def z1177 : W := mkw 0x2ba950006e960008 0x02ba950006e96000 0xa3fff0004fff000d 0xfa3fff0004fff000

def z1178 : W := mkw 0x2f9d4113b7e488c9 0xc2f9d4113b7e488c 0x4f180333b7c09988 0x24f180333b7c0998

def z1179 : W := mkw 0x4ed6efff00000000 0x04ed6efff0000000 0x4fe67fff80000002 0xf4fe67fff8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z7,z8]),(0,[z9,z1,z2,z3,z10,z4,z5]),(0,[z1,z11,z2,z12,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z14]),(1,[z15,z1,z2,z4,z16,z13])],[(0,[z1,z2,z3,z4,z5,z7,z17]),(1,[z1,z2,z3,z4,z18,z13]),(0,[z1,z2,z3,z4,z5,z13,z19])],[(0,[z1,z2,z20,z3,z4,z5,z13])],[(0,[z1,z2,z3,z21,z4,z5,z13]),(0,[z1,z2,z3,z22,z23,z5,z13]),(0,[z1,z2,z3,z24,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z25,z13])],[(0,[z1,z2,z3,z4,z26,z5,z13]),(0,[z27,z1,z2,z3,z4,z28,z13])],[(0,[z29,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z30,z13])],[(1,[z1,z2,z31,z4,z5,z13]),(1,[z1,z2,z3,z4,z32,z5])],[(0,[z33,z1,z2,z3,z5,z34,z13]),(0,[z1,z2,z3,z4,z35,z5,z13]),(0,[z1,z2,z3,z4,z5,z36,z13]),(0,[z37,z1,z2,z3,z4,z5,z13])]],
   [[(1,[z38,z2,z3,z4,z34,z13]),(0,[z1,z2,z3,z10,z4,z5,z7]),(0,[z1,z2,z3,z39,z4,z5,z25])],[(0,[z40,z1,z2,z3,z4,z5,z13])],[(0,[z41,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z42,z5,z13]),(0,[z9,z43,z2,z3,z4,z5,z13]),(0,[z44,z1,z2,z3,z4,z45,z13])],[(0,[z46,z1,z2,z47,z4,z5,z13]),(0,[z1,z2,z48,z3,z4,z5,z13]),(0,[z1,z2,z3,z49,z4,z5,z13]),(0,[z1,z2,z3,z4,z50,z5,z13])],[(0,[z51,z1,z2,z3,z52,z5,z13]),(0,[z43,z1,z2,z3,z4,z45,z5]),(0,[z44,z1,z53,z2,z3,z4,z13]),(0,[z54,z1,z3,z4,z55,z5,z13]),(0,[z1,z2,z3,z4,z5,z56,z57]),(0,[z1,z2,z3,z58,z4,z5,z13])],[(0,[z1,z59,z2,z3,z4,z5,z13]),(0,[z2,z3,z4,z28,z5,z34,z13]),(0,[z60,z1,z2,z3,z4,z5,z13]),(0,[z61,z44,z1,z2,z3,z5,z13]),(0,[z1,z2,z4,z5,z7,z13,z57]),(0,[z1,z62,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z10,z5,z25,z13])],[(0,[z63,z46,z2,z3,z4,z5,z13]),(0,[z15,z1,z2,z4,z64,z5,z13])],[(0,[z65,z1,z2,z3,z4,z5,z13]),(0,[z66,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z67,z13,z68]),(0,[z1,z2,z3,z5,z67,z13,z69])]],
   [[(0,[z70,z1,z2,z3,z5,z71,z13])],[(0,[z1,z2,z3,z4,z5,z72,z13]),(0,[z43,z1,z2,z3,z39,z4,z5]),(0,[z1,z11,z2,z3,z4,z5,z13]),(0,[z73,z1,z2,z3,z4,z5,z74]),(0,[z1,z2,z3,z4,z75,z67,z13])],[(0,[z1,z76,z2,z3,z4,z5,z13]),(0,[z27,z2,z3,z4,z28,z5,z13])],[(0,[z1,z2,z3,z4,z5,z77,z13])],[(0,[z46,z1,z2,z78,z4,z5,z13]),(0,[z79,z1,z2,z3,z4,z5,z13]),(0,[z1,z53,z2,z3,z4,z71,z13]),(0,[z1,z2,z3,z4,z5,z17,z80]),(0,[z1,z2,z3,z4,z5,z7,z13])],[(0,[z1,z2,z3,z81,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z82,z13])],[(0,[z1,z2,z3,z4,z83,z5,z13]),(0,[z1,z84,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z85,z5,z13]),(0,[z1,z2,z3,z86,z4,z5,z13]),(1,[z1,z2,z3,z4,z5,z87]),(0,[z1,z2,z3,z4,z5,z13,z88]),(0,[z1,z2,z3,z4,z5,z89,z13]),(0,[z1,z2,z3,z4,z16,z5,z13]),(0,[z1,z2,z3,z90,z4,z5,z13]),(1,[z44,z1,z2,z3,z91,z13])]],
   [[(0,[z1,z2,z3,z4,z5,z92,z13]),(0,[z1,z2,z22,z4,z64,z5,z13]),(0,[z93,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z25,z13,z94])],[(0,[z1,z2,z3,z4,z95,z5,z13]),(0,[z1,z2,z3,z4,z5,z96,z80]),(0,[z1,z2,z3,z97,z4,z5,z71])],[(0,[z1,z2,z3,z4,z5,z13,z98]),(0,[z1,z2,z3,z4,z99,z5,z13]),(0,[z100,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z101,z5,z13])],[(0,[z102,z1,z103,z3,z4,z5,z13]),(0,[z104,z1,z2,z3,z4,z5,z13]),(0,[z105,z1,z2,z3,z106,z5,z13]),(0,[z107,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z108,z3,z4,z5,z13]),(0,[z1,z2,z109,z3,z4,z5,z13]),(0,[z110,z1,z2,z3,z5,z13,z80]),(0,[z1,z2,z3,z111,z4,z5,z13])],[(0,[z112,z1,z2,z3,z4,z5,z13]),(0,[z1,z113,z2,z3,z4,z114,z5]),(0,[z33,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z115,z4,z5,z13]),(0,[z116,z1,z2,z3,z4,z5,z13]),(0,[z117,z1,z2,z3,z4,z5,z13]),(0,[z1,z118,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z13,z119]),(0,[z1,z2,z3,z4,z28,z75,z13]),(0,[z1,z3,z4,z5,z17,z13,z56]),(0,[z1,z2,z3,z4,z120,z5,z13])],[(1,[z121,z1,z2,z64,z5,z13]),(0,[z1,z2,z3,z4,z122,z5,z13]),(0,[z1,z2,z3,z123,z4,z5,z13])],[(0,[z1,z2,z3,z124,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z125])]],
   [[(0,[z1,z126,z2,z3,z4,z5,z13]),(0,[z127,z1,z2,z3,z4,z5,z13]),(0,[z61,z1,z128,z3,z4,z5,z13]),(0,[z1,z53,z2,z3,z4,z55,z13]),(0,[z1,z2,z3,z4,z129,z5,z13])],[(0,[z1,z2,z3,z4,z130,z5,z13])],[(0,[z1,z2,z3,z4,z5,z131,z13]),(0,[z38,z1,z2,z3,z4,z5,z132]),(0,[z1,z2,z3,z4,z5,z13,z133]),(0,[z1,z134,z3,z4,z5,z13,z56]),(0,[z1,z2,z3,z4,z5,z13,z56]),(0,[z1,z2,z3,z135,z4,z5,z13]),(0,[z1,z2,z136,z4,z5,z13,z57]),(1,[z1,z2,z3,z4,z5,z137])],[(0,[z138,z1,z2,z3,z4,z5,z13])],[(1,[z1,z2,z3,z106,z5,z13]),(0,[z0,z51,z2,z3,z4,z5,z13]),(0,[z1,z2,z139,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z140,z13]),(0,[z1,z2,z3,z4,z5,z13,z141]),(0,[z1,z2,z142,z3,z4,z16,z13]),(0,[z1,z143,z2,z3,z4,z5,z13]),(0,[z1,z2,z144,z3,z4,z5,z13])],[(0,[z1,z2,z3,z145,z4,z5,z13]),(0,[z1,z2,z146,z3,z4,z5,z13]),(0,[z44,z1,z2,z3,z64,z5,z13]),(0,[z1,z2,z3,z4,z5,z147,z13]),(0,[z1,z2,z3,z4,z148,z5,z13])],[(0,[z63,z1,z2,z3,z4,z5,z13]),(0,[z46,z2,z103,z3,z4,z5,z13]),(0,[z149,z1,z2,z3,z4,z5,z13]),(0,[z73,z1,z2,z3,z35,z5,z13]),(0,[z1,z128,z2,z3,z150,z5,z13]),(1,[z1,z2,z3,z4,z5,z151]),(1,[z1,z2,z3,z152,z5,z13]),(0,[z1,z2,z3,z39,z4,z5,z13]),(0,[z153,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z154,z3,z4,z5,z13]),(0,[z61,z1,z2,z3,z23,z5,z13]),(0,[z1,z155,z2,z3,z4,z5,z13])]],
   [[(0,[z156,z1,z2,z3,z4,z5,z13]),(0,[z63,z1,z157,z3,z4,z5,z13]),(0,[z1,z2,z158,z3,z4,z5,z13]),(0,[z27,z1,z2,z3,z4,z34,z13]),(0,[z1,z2,z3,z4,z5,z159,z13]),(0,[z1,z160,z2,z3,z4,z5,z13]),(0,[z54,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z22,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z161,z13]),(0,[z162,z1,z2,z3,z163,z5,z13]),(0,[z1,z2,z3,z4,z45,z5,z68])],[(0,[z1,z2,z3,z4,z5,z164,z13]),(0,[z63,z157,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z165]),(0,[z1,z2,z3,z4,z5,z166,z13]),(0,[z1,z2,z3,z4,z167,z5,z13]),(0,[z1,z2,z3,z39,z4,z5,z57])],[(0,[z1,z2,z3,z4,z5,z13,z132]),(0,[z1,z2,z3,z4,z5,z168,z13]),(0,[z1,z2,z3,z4,z169,z5,z13]),(0,[z1,z2,z170,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z171,z13]),(0,[z15,z1,z2,z3,z4,z75,z13]),(0,[z1,z2,z3,z4,z5,z172,z13])],[(0,[z1,z2,z3,z4,z5,z173,z13]),(0,[z174,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z175,z13]),(1,[z1,z2,z3,z39,z4,z68])],[(0,[z1,z2,z3,z176,z4,z5,z13]),(0,[z1,z2,z3,z177,z4,z5,z13])],[(0,[z105,z1,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z4,z5,z13,z178]),(0,[z179,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z5,z13]),(0,[z180,z1,z2,z3,z4,z5,z13])],[(0,[z102,z2,z103,z3,z4,z5,z13]),(0,[z1,z134,z2,z3,z4,z5,z96]),(0,[z181,z1,z2,z3,z4,z5,z13])]],
   [[(1,[z1,z11,z12,z4,z5,z13]),(1,[z1,z2,z3,z182,z5,z13]),(0,[z1,z134,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z183,z5,z13]),(0,[z1,z184,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z13,z185]),(0,[z1,z128,z2,z3,z186,z5,z13]),(0,[z44,z1,z2,z3,z5,z91,z13]),(0,[z1,z2,z3,z90,z4,z45,z13])],[(0,[z187,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z188,z3,z4,z5,z13]),(1,[z1,z2,z3,z10,z5,z25]),(0,[z189,z1,z2,z3,z4,z5,z13])],[(0,[z190,z1,z2,z3,z4,z5,z13]),(0,[z1,z53,z2,z3,z4,z5,z191]),(0,[z1,z2,z3,z4,z5,z13,z192])],[(0,[z1,z2,z3,z193,z4,z5,z13]),(0,[z194,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z195,z5,z13]),(0,[z110,z1,z2,z3,z4,z5,z25])],[(0,[z196,z1,z2,z3,z4,z5,z13]),(0,[z44,z51,z1,z2,z3,z5,z13]),(0,[z1,z2,z3,z4,z197,z5,z13]),(0,[z1,z2,z198,z3,z4,z5,z13])],[(0,[z1,z2,z3,z199,z4,z5,z13]),(1,[z1,z2,z3,z4,z5,z131]),(0,[z200,z1,z2,z3,z4,z5,z13]),(1,[z1,z201,z2,z3,z4,z13]),(0,[z202,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z203,z3,z4,z5,z13]),(0,[z204,z1,z2,z3,z4,z5,z13]),(0,[z205,z1,z2,z3,z4,z5,z13])]],
   [[],[(0,[z1,z2,z103,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z206]),(0,[z0,z44,z1,z2,z3,z5,z13])],[(0,[z1,z2,z3,z10,z4,z5,z25])],[(0,[z1,z2,z207,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z208]),(0,[z1,z2,z3,z4,z209,z5,z13]),(0,[z1,z2,z3,z210,z5,z67,z13])],[(0,[z1,z2,z3,z4,z211,z5,z13]),(0,[z1,z2,z3,z4,z5,z67,z56]),(0,[z1,z212,z2,z3,z4,z5,z13]),(0,[z213,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z39,z4,z5,z68])],[(0,[z102,z1,z2,z3,z4,z5,z13]),(0,[z214,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z215,z4,z5,z13]),(0,[z105,z1,z216,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z217,z13]),(0,[z1,z2,z3,z4,z5,z13,z218]),(0,[z1,z2,z3,z4,z219,z5,z13]),(1,[z1,z2,z3,z90,z150,z13])],[(0,[z1,z220,z2,z3,z4,z5,z13]),(0,[z1,z221,z2,z3,z4,z5,z13]),(0,[z1,z222,z2,z3,z4,z5,z13])]],
   [[(0,[z102,z1,z157,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z223]),(0,[z1,z2,z3,z4,z55,z5,z13]),(0,[z1,z2,z3,z4,z224,z5,z13]),(0,[z1,z2,z3,z39,z4,z45,z13])],[(0,[z105,z1,z2,z3,z225,z5,z13]),(0,[z1,z2,z3,z4,z226,z5,z13]),(0,[z51,z1,z2,z3,z150,z5,z13]),(0,[z1,z2,z3,z23,z4,z5,z13]),(0,[z61,z1,z2,z3,z4,z5,z227]),(0,[z1,z2,z3,z228,z4,z5,z13]),(1,[z1,z134,z3,z4,z5,z56]),(0,[z229,z1,z2,z3,z4,z5,z13])],[(0,[z2,z103,z3,z78,z4,z5,z13]),(0,[z105,z2,z3,z78,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z230,z13]),(0,[z43,z1,z2,z3,z4,z5,z56]),(0,[z9,z1,z2,z3,z4,z5,z96]),(0,[z1,z2,z3,z231,z4,z5,z13]),(0,[z1,z2,z232,z3,z4,z5,z13]),(0,[z162,z1,z2,z3,z4,z5,z7])],[(0,[z43,z1,z2,z3,z10,z4,z5]),(1,[z1,z2,z3,z4,z5,z233])],[(0,[z44,z38,z1,z2,z3,z4,z13]),(1,[z1,z2,z3,z4,z5,z234]),(0,[z235,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z236])],[(0,[z1,z2,z3,z3,z4,z5,z13]),(0,[z1,z2,z3,z237,z4,z5,z13]),(0,[z1,z2,z238,z3,z4,z5,z13]),(0,[z27,z1,z2,z3,z90,z4,z13])],[(0,[z1,z2,z3,z4,z239,z5,z13]),(0,[z1,z240,z2,z3,z4,z5,z13]),(0,[z241,z1,z2,z3,z4,z5,z13]),(0,[z1,z11,z2,z242,z4,z5,z13]),(1,[z1,z2,z3,z115,z4,z13]),(0,[z107,z1,z2,z3,z4,z45,z5]),(0,[z1,z2,z3,z4,z5,z13,z243])],[(1,[z1,z216,z3,z4,z5,z13]),(1,[z0,z2,z3,z114,z5,z13]),(0,[z1,z2,z3,z4,z244,z5,z13]),(1,[z162,z1,z2,z4,z5,z7])]],
   [[(0,[z245,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z22,z52,z5,z13]),(0,[z1,z2,z3,z4,z5,z246,z13]),(0,[z1,z2,z3,z247,z4,z5,z13]),(0,[z248,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z163,z5,z13])],[(0,[z1,z249,z2,z3,z4,z5,z13]),(0,[z1,z134,z2,z3,z4,z5,z17]),(0,[z250,z1,z2,z3,z4,z5,z13]),(0,[z1,z251,z2,z3,z4,z5,z13])],[(0,[z252,z1,z2,z3,z4,z5,z13]),(0,[z1,z216,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z225,z5,z13]),(1,[z1,z2,z3,z4,z5,z132]),(0,[z1,z2,z3,z4,z253,z5,z13]),(0,[z44,z1,z2,z3,z4,z75,z13])],[(0,[z254,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z255,z13]),(0,[z1,z2,z3,z4,z32,z5,z13]),(0,[z1,z2,z3,z256,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z56,z80]),(0,[z107,z1,z2,z3,z39,z4,z5]),(0,[z44,z1,z2,z3,z10,z5,z13]),(0,[z1,z2,z257,z3,z4,z5,z13])],[(0,[z258,z1,z2,z3,z4,z5,z13]),(0,[z51,z2,z3,z52,z4,z5,z13]),(0,[z61,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z259,z5,z13]),(1,[z1,z2,z3,z4,z5,z260]),(0,[z261,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z262,z4,z5,z13]),(0,[z1,z2,z3,z4,z4,z5,z13]),(0,[z1,z2,z3,z4,z263,z5,z13]),(0,[z27,z44,z1,z2,z3,z4,z13]),(0,[z1,z2,z12,z3,z4,z5,z13]),(0,[z1,z2,z3,z264,z4,z5,z13]),(0,[z110,z1,z2,z3,z22,z5,z13])],[(1,[z70,z1,z2,z3,z5,z13]),(0,[z1,z2,z3,z4,z5,z265,z13])]],
   [[(0,[z1,z266,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z25,z56]),(0,[z267,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z268,z5,z13])],[(0,[z44,z1,z2,z3,z4,z91,z13])],[(0,[z1,z2,z3,z4,z5,z269,z13]),(0,[z1,z2,z3,z4,z5,z270,z13]),(0,[z271,z1,z2,z3,z4,z5,z13]),(0,[z110,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z272,z13]),(0,[z1,z2,z3,z4,z5,z273,z13]),(0,[z1,z2,z3,z90,z4,z16,z13])],[(0,[z274,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z275,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z276]),(1,[z1,z2,z3,z4,z277,z13]),(0,[z278,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z279,z13]),(0,[z280,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z45,z5,z13])],[(0,[z1,z2,z3,z281,z4,z5,z13]),(0,[z110,z1,z2,z3,z4,z5,z57])],[(0,[z1,z2,z3,z4,z282,z5,z13]),(0,[z1,z2,z3,z4,z5,z283,z13]),(1,[z54,z1,z3,z4,z55,z13]),(0,[z1,z2,z3,z4,z5,z13,z284]),(0,[z1,z2,z3,z4,z5,z285,z13]),(0,[z1,z2,z286,z3,z4,z5,z161]),(0,[z1,z2,z3,z4,z287,z5,z13])],[(0,[z51,z1,z2,z3,z114,z5,z13]),(0,[z1,z288,z2,z3,z4,z5,z13]),(0,[z289,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z45,z5,z57]),(0,[z1,z2,z3,z4,z290,z5,z13])]],
   [[(0,[z1,z2,z3,z4,z5,z291,z13]),(0,[z1,z2,z3,z4,z5,z292,z13]),(0,[z1,z2,z3,z293,z4,z5,z13]),(0,[z1,z2,z3,z294,z4,z5,z13]),(0,[z1,z2,z3,z10,z4,z5,z13]),(0,[z295,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z45,z67])],[(0,[z1,z2,z3,z4,z296,z5,z13]),(0,[z1,z2,z3,z297,z4,z5,z13]),(0,[z298,z1,z2,z3,z4,z5,z13]),(0,[z1,z299,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z300,z4,z5,z13]),(1,[z1,z2,z3,z210,z5,z13])],[(0,[z301,z1,z2,z3,z4,z5,z13]),(0,[z121,z1,z2,z3,z22,z5,z13]),(0,[z302,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z303,z4,z5,z13]),(0,[z73,z304,z2,z3,z4,z5,z13]),(0,[z61,z1,z3,z4,z186,z5,z13]),(0,[z1,z2,z3,z10,z4,z5,z57])],[(0,[z1,z2,z2,z3,z4,z5,z13]),(0,[z1,z103,z3,z242,z4,z5,z13]),(0,[z9,z1,z2,z3,z4,z5,z17]),(0,[z73,z1,z2,z12,z4,z5,z13]),(0,[z305,z1,z2,z3,z4,z5,z13])],[(0,[z306,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z307,z5,z13])],[(0,[z308,z1,z2,z3,z4,z5,z13]),(0,[z309,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z310,z13]),(0,[z311,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z312,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z313,z5,z13]),(0,[z1,z314,z2,z3,z4,z5,z13]),(0,[z15,z1,z2,z4,z16,z5,z13]),(0,[z315,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z316,z13])]],
   [[(1,[z1,z2,z3,z4,z5,z317]),(0,[z1,z2,z3,z318,z5,z34,z13]),(1,[z1,z2,z3,z4,z5,z319]),(0,[z44,z1,z2,z144,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z320,z13])],[(0,[z321,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z322,z4,z5,z13]),(0,[z1,z2,z3,z4,z71,z75,z13]),(0,[z1,z2,z3,z182,z5,z71,z13]),(0,[z107,z1,z3,z4,z5,z17,z13]),(0,[z1,z2,z3,z39,z4,z16,z13]),(0,[z1,z2,z3,z4,z323,z5,z13])],[(0,[z1,z2,z3,z4,z5,z13,z324])],[(0,[z1,z2,z286,z3,z22,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z325])],[(0,[z1,z2,z3,z326,z4,z5,z13]),(0,[z1,z2,z3,z4,z16,z34,z13]),(0,[z1,z2,z3,z4,z327,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z328]),(0,[z1,z2,z3,z4,z5,z329,z13]),(1,[z1,z2,z144,z4,z5,z13]),(0,[z44,z1,z2,z3,z90,z5,z13]),(0,[z1,z2,z3,z90,z4,z5,z233])],[(0,[z73,z46,z1,z2,z4,z5,z13]),(0,[z1,z2,z3,z330,z4,z5,z13]),(0,[z1,z2,z3,z4,z32,z5,z34]),(0,[z1,z2,z3,z4,z5,z13,z331]),(0,[z1,z2,z3,z4,z332,z5,z13])],[(0,[z15,z1,z2,z286,z4,z5,z13]),(0,[z1,z333,z2,z3,z4,z5,z13])]],
   [[(0,[z334,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z335,z13]),(0,[z1,z2,z3,z4,z34,z75,z13]),(0,[z1,z2,z336,z3,z4,z5,z13]),(0,[z9,z110,z1,z2,z3,z4,z5]),(0,[z337,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z286,z3,z4,z5,z13]),(0,[z1,z2,z3,z39,z4,z5,z80])],[(0,[z338,z1,z2,z3,z4,z5,z13]),(0,[z1,z157,z2,z3,z4,z5,z339]),(0,[z340,z1,z2,z3,z4,z5,z13]),(0,[z304,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z16,z55,z13]),(0,[z110,z1,z2,z3,z4,z5,z68])],[(0,[z1,z2,z341,z3,z4,z5,z13]),(0,[z342,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z343,z4,z5,z13]),(0,[z1,z344,z2,z3,z4,z5,z13])],[(0,[z44,z1,z2,z3,z4,z13,z68])],[(0,[z1,z2,z3,z4,z5,z345,z13]),(0,[z1,z2,z346,z3,z4,z5,z13]),(0,[z1,z2,z3,z90,z150,z5,z13])],[(0,[z347,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z348,z5,z13]),(0,[z73,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z349,z13]),(0,[z15,z1,z2,z3,z350,z5,z13])],[(0,[z73,z1,z2,z3,z231,z5,z13]),(0,[z1,z2,z142,z4,z5,z75,z13])],[(0,[z1,z2,z3,z4,z5,z13,z351]),(0,[z352,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z90,z4,z5,z260]),(0,[z1,z2,z3,z10,z4,z5,z68]),(0,[z1,z2,z3,z39,z4,z5,z67])]],
   [[(0,[z102,z63,z2,z3,z4,z5,z13]),(0,[z1,z2,z353,z3,z4,z5,z13]),(0,[z1,z2,z3,z354,z4,z5,z13]),(0,[z1,z2,z3,z4,z355,z5,z13]),(0,[z1,z2,z3,z4,z356,z5,z13])],[(0,[z357,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z358,z3,z4,z5,z13]),(1,[z359,z2,z3,z4,z5,z13]),(0,[z360,z1,z2,z3,z4,z5,z13])],[(0,[z361,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z362,z13])],[(0,[z1,z2,z3,z4,z5,z363,z13]),(0,[z364,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z365,z4,z5,z13]),(1,[z1,z2,z3,z5,z13,z69])],[(0,[z1,z2,z3,z4,z366,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z367])],[(0,[z368,z1,z2,z3,z4,z5,z13]),(0,[z110,z1,z134,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z96,z25]),(0,[z73,z1,z11,z3,z4,z5,z13]),(0,[z1,z2,z369,z3,z4,z5,z13]),(0,[z1,z2,z3,z370,z4,z186,z5]),(0,[z44,z1,z2,z3,z5,z13,z80])],[(0,[z105,z1,z2,z3,z4,z371,z13]),(0,[z1,z372,z2,z3,z4,z5,z13]),(0,[z1,z2,z373,z3,z4,z5,z13])]],
   [[(0,[z46,z1,z2,z3,z4,z5,z13]),(0,[z105,z1,z2,z3,z4,z226,z13]),(0,[z0,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z374,z4,z5,z13]),(0,[z1,z2,z3,z375,z4,z5,z13]),(0,[z1,z2,z3,z150,z5,z91,z13])],[(0,[z1,z2,z3,z4,z5,z13,z74]),(0,[z1,z12,z3,z242,z4,z5,z13])],[(0,[z376,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z377,z3,z4,z186,z5]),(0,[z1,z2,z3,z378,z4,z5,z13]),(0,[z1,z2,z3,z150,z5,z13,z80])],[(0,[z1,z2,z31,z103,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z379,z13]),(0,[z38,z2,z3,z4,z5,z34,z13]),(1,[z1,z2,z3,z318,z5,z13]),(0,[z1,z2,z380,z3,z4,z5,z13]),(0,[z121,z1,z2,z286,z4,z5,z13]),(0,[z162,z1,z2,z136,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z381])],[(0,[z63,z2,z3,z78,z4,z5,z13]),(0,[z1,z2,z3,z275,z4,z114,z5]),(0,[z1,z2,z382,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z34,z13]),(1,[z43,z2,z3,z4,z5,z8]),(0,[z107,z1,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z383,z13]),(0,[z1,z2,z3,z4,z5,z13,z384]),(0,[z1,z2,z3,z4,z5,z385,z13])],[(0,[z1,z2,z3,z4,z106,z5,z13]),(0,[z386,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z387,z1,z2,z3,z4,z5,z13]),(1,[z9,z2,z3,z4,z5,z96]),(0,[z107,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z22,z150,z5,z13])],[(0,[z1,z2,z3,z4,z5,z339,z13]),(1,[z51,z2,z3,z52,z5,z13]),(0,[z388,z1,z2,z3,z4,z5,z13]),(0,[z389,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z390,z13])],[(0,[z1,z2,z3,z4,z391,z5,z13]),(0,[z1,z2,z3,z4,z5,z67,z96]),(0,[z1,z2,z3,z392,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z393,z13])]],
   [[(0,[z1,z2,z3,z4,z5,z394,z13]),(1,[z1,z2,z3,z4,z371,z13]),(0,[z1,z2,z3,z395,z4,z114,z13]),(0,[z1,z2,z396,z3,z4,z5,z13])],[(1,[z1,z2,z3,z4,z226,z13]),(0,[z397,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z398,z4,z5,z13]),(0,[z1,z2,z3,z4,z399,z5,z13]),(0,[z162,z1,z2,z3,z4,z400,z13])],[(0,[z1,z2,z3,z4,z5,z401,z13]),(0,[z1,z2,z3,z402,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z403,z13])],[(0,[z1,z2,z3,z4,z5,z404,z13]),(0,[z1,z2,z3,z4,z405,z5,z13]),(0,[z1,z2,z3,z4,z64,z5,z13])],[(0,[z1,z2,z3,z406,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z6,z13]),(0,[z1,z2,z3,z4,z16,z28,z13]),(0,[z407,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z408,z3,z4,z5,z13]),(0,[z43,z1,z2,z3,z4,z5,z96]),(0,[z1,z2,z142,z3,z4,z75,z13]),(0,[z15,z1,z2,z3,z4,z5,z409])],[(0,[z1,z2,z3,z4,z410,z5,z13]),(0,[z1,z2,z411,z3,z4,z5,z13]),(0,[z1,z2,z412,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z413,z5,z13])],[(0,[z1,z201,z2,z3,z4,z114,z13]),(0,[z2,z3,z4,z5,z96,z13,z8]),(0,[z1,z2,z3,z4,z5,z13,z227]),(0,[z1,z2,z3,z4,z5,z13,z414]),(0,[z110,z1,z2,z3,z64,z5,z13]),(1,[z1,z2,z3,z4,z5,z141]),(0,[z1,z2,z3,z4,z415,z5,z13])]],
   [[(0,[z105,z1,z2,z78,z4,z5,z13]),(0,[z1,z2,z3,z4,z416,z5,z13]),(0,[z1,z2,z3,z22,z186,z5,z13]),(0,[z1,z2,z3,z370,z4,z5,z13]),(1,[z1,z2,z286,z22,z5,z13]),(0,[z1,z2,z4,z16,z5,z75,z13])],[(0,[z1,z2,z3,z4,z182,z5,z13]),(0,[z1,z2,z417,z3,z4,z5,z13]),(0,[z1,z2,z418,z3,z4,z5,z13])],[(0,[z419,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z420,z5,z13]),(0,[z1,z2,z3,z4,z5,z421,z13]),(0,[z38,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z422,z4,z5,z13])],[(0,[z1,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z423,z3,z4,z5,z13]),(0,[z1,z134,z2,z3,z4,z5,z8]),(0,[z73,z1,z3,z242,z4,z5,z13]),(0,[z1,z53,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z424,z13])],[(1,[z1,z2,z3,z97,z4,z5])],[(1,[z1,z203,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z277,z13]),(0,[z1,z2,z3,z4,z5,z425,z13]),(0,[z426,z1,z2,z3,z4,z5,z13]),(0,[z15,z1,z2,z3,z4,z5,z13])],[(0,[z1,z157,z2,z3,z4,z5,z13]),(0,[z1,z2,z286,z22,z4,z5,z13])],[(0,[z1,z2,z3,z4,z427,z5,z13]),(0,[z15,z1,z2,z3,z268,z5,z13]),(0,[z1,z2,z136,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z91,z13])]],
   [[(0,[z1,z2,z3,z428,z4,z5,z13]),(0,[z1,z2,z3,z429,z4,z5,z13]),(0,[z430,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z431,z3,z4,z5,z13]),(0,[z1,z432,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z433,z4,z5,z13])],[(1,[z1,z2,z3,z395,z4,z13]),(0,[z1,z2,z3,z4,z5,z434,z13])],[(0,[z1,z2,z3,z4,z5,z435,z13]),(0,[z1,z2,z3,z4,z5,z13,z13]),(1,[z1,z2,z3,z350,z5,z13]),(0,[z1,z2,z136,z3,z4,z5,z57]),(0,[z1,z2,z3,z90,z4,z13,z68])],[(0,[z436,z1,z2,z3,z4,z5,z13]),(0,[z105,z1,z2,z3,z4,z5,z206]),(0,[z1,z2,z3,z22,z114,z5,z13]),(0,[z1,z2,z3,z437,z4,z5,z13]),(0,[z54,z1,z2,z3,z90,z4,z13]),(0,[z1,z2,z3,z4,z5,z438,z13]),(0,[z1,z2,z3,z39,z4,z5,z7]),(0,[z439,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z440,z13])],[(0,[z1,z2,z3,z441,z4,z5,z13]),(0,[z442,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z443,z13]),(0,[z110,z1,z2,z3,z4,z5,z80])],[(0,[z1,z2,z3,z4,z5,z13,z444]),(0,[z1,z2,z3,z4,z445,z5,z13]),(0,[z446,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z16,z67,z13]),(0,[z1,z2,z3,z4,z5,z13,z57])],[(1,[z1,z2,z3,z4,z445,z13]),(0,[z1,z2,z3,z447,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z233,z13]),(0,[z1,z2,z3,z4,z45,z5,z80])],[(0,[z1,z2,z448,z3,z4,z5,z13]),(0,[z1,z157,z11,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z449,z5,z13]),(0,[z450,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z275,z4,z5]),(0,[z1,z451,z2,z3,z4,z5,z13]),(0,[z44,z1,z2,z452,z4,z5,z13]),(0,[z1,z2,z3,z4,z453,z5,z13])]],
   [[(0,[z1,z2,z3,z4,z454,z5,z13]),(0,[z1,z2,z3,z455,z4,z5,z13]),(0,[z0,z1,z2,z3,z52,z5,z13]),(0,[z1,z2,z3,z395,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z456,z13]),(0,[z1,z2,z3,z4,z5,z457,z13])],[(0,[z458,z1,z2,z3,z4,z5,z13]),(0,[z1,z459,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z67,z17])],[(0,[z1,z2,z3,z460,z4,z5,z13]),(1,[z1,z113,z2,z3,z4,z5]),(0,[z1,z461,z2,z3,z4,z5,z13]),(0,[z462,z1,z2,z3,z4,z5,z13]),(1,[z107,z1,z3,z4,z5,z17]),(0,[z1,z2,z3,z10,z4,z5,z80])],[(0,[z1,z2,z3,z463,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z464,z13]),(0,[z1,z2,z3,z4,z150,z5,z403]),(0,[z110,z1,z2,z3,z4,z5,z67])],[(0,[z1,z2,z3,z4,z5,z13,z465]),(1,[z1,z2,z3,z4,z5,z206]),(0,[z1,z2,z3,z4,z466,z5,z13]),(0,[z467,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z452,z4,z5,z13])],[(0,[z468,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z5,z191]),(0,[z1,z2,z286,z3,z64,z5,z13]),(0,[z1,z2,z286,z3,z4,z171,z13]),(0,[z1,z2,z3,z4,z45,z5,z67])],[(0,[z105,z1,z11,z2,z4,z5,z13]),(0,[z9,z1,z2,z3,z4,z5,z8]),(0,[z469,z1,z2,z3,z4,z5,z13]),(0,[z162,z1,z2,z3,z4,z18,z13])],[(0,[z470,z1,z2,z3,z4,z5,z13]),(0,[z471,z1,z2,z3,z4,z5,z13]),(0,[z1,z201,z2,z3,z4,z5,z13]),(0,[z27,z38,z2,z3,z4,z5,z13]),(0,[z43,z1,z2,z3,z4,z5,z17]),(0,[z1,z134,z2,z3,z4,z5,z13]),(0,[z472,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z152,z4,z5,z13]),(0,[z1,z2,z473,z3,z4,z5,z13])]],
   [[(0,[z1,z474,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z475,z13]),(0,[z1,z2,z3,z4,z16,z71,z13]),(0,[z1,z2,z3,z64,z150,z5,z13]),(1,[z1,z2,z3,z4,z5,z161])],[(0,[z1,z2,z3,z4,z5,z476,z13]),(0,[z1,z2,z477,z3,z4,z5,z13]),(0,[z38,z1,z2,z3,z4,z5,z173]),(0,[z61,z1,z2,z3,z150,z5,z13]),(0,[z121,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z478,z5,z13]),(0,[z1,z2,z3,z4,z163,z5,z13]),(1,[z1,z2,z3,z4,z400,z13]),(0,[z1,z2,z3,z4,z5,z13,z479]),(0,[z1,z2,z3,z10,z4,z5,z67]),(0,[z1,z2,z3,z39,z4,z13,z68]),(0,[z1,z2,z3,z4,z5,z13,z480])],[(0,[z1,z2,z481,z3,z4,z5,z13]),(0,[z1,z3,z4,z55,z5,z71,z13]),(0,[z1,z2,z3,z4,z482,z5,z13])],[(0,[z54,z1,z53,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z483,z5,z13]),(0,[z1,z2,z3,z484,z4,z5,z13]),(0,[z1,z2,z3,z4,z150,z5,z13])],[(0,[z0,z1,z2,z3,z4,z5,z485]),(0,[z1,z2,z3,z4,z5,z7,z96]),(0,[z1,z2,z3,z486,z4,z5,z13]),(1,[z1,z128,z3,z23,z5,z13]),(0,[z1,z2,z3,z4,z5,z7,z56]),(0,[z162,z1,z2,z4,z5,z7,z13]),(0,[z1,z2,z487,z3,z4,z5,z13])],[(0,[z1,z2,z3,z488,z4,z5,z13]),(0,[z489,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z490,z5,z13]),(0,[z1,z2,z3,z4,z491,z5,z13]),(0,[z492,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z493,z3,z4,z5,z13])],[(0,[z494,z1,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z114,z5,z13]),(0,[z1,z2,z3,z4,z5,z495,z13]),(0,[z73,z359,z2,z3,z4,z5,z13]),(0,[z496,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z349,z13]),(0,[z1,z2,z3,z4,z5,z497,z13]),(0,[z1,z2,z3,z498,z4,z5,z13])],[(0,[z70,z1,z2,z3,z4,z5,z13]),(0,[z1,z499,z2,z3,z4,z5,z13]),(0,[z1,z2,z500,z3,z4,z5,z13]),(0,[z1,z2,z3,z501,z4,z5,z13])]],
   [[(0,[z1,z2,z502,z3,z4,z5,z13]),(0,[z1,z2,z3,z52,z4,z5,z13])],[(0,[z1,z2,z3,z503,z4,z5,z13]),(0,[z44,z1,z2,z3,z22,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z68])],[(0,[z1,z2,z31,z3,z4,z5,z13]),(0,[z1,z2,z3,z504,z4,z5,z13]),(1,[z1,z2,z3,z4,z5,z409]),(0,[z505,z1,z2,z3,z4,z5,z13])],[(0,[z1,z11,z103,z3,z4,z5,z13]),(0,[z1,z506,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z507,z13])],[(0,[z1,z157,z3,z242,z4,z5,z13]),(0,[z1,z2,z3,z4,z508,z5,z13]),(0,[z61,z1,z2,z3,z186,z5,z13]),(0,[z1,z128,z2,z3,z23,z5,z13]),(0,[z509,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z510,z5,z13]),(0,[z1,z2,z3,z4,z5,z67,z13])],[(0,[z1,z2,z3,z511,z4,z5,z13]),(0,[z1,z53,z2,z3,z4,z5,z87]),(0,[z1,z2,z3,z4,z5,z512,z13]),(0,[z1,z513,z2,z3,z4,z5,z13]),(0,[z514,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z515,z13])],[(0,[z1,z2,z3,z4,z516,z5,z13]),(0,[z517,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z35,z5,z13]),(0,[z1,z2,z3,z4,z186,z5,z13]),(0,[z1,z2,z3,z4,z518,z5,z13]),(0,[z1,z2,z3,z4,z519,z5,z13])],[(0,[z2,z3,z52,z4,z114,z5,z13]),(0,[z520,z1,z2,z3,z4,z5,z13])]],
   [[(0,[z1,z2,z3,z4,z521,z5,z13]),(0,[z1,z2,z3,z97,z4,z5,z13]),(0,[z522,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z523,z13]),(0,[z524,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z225,z4,z5,z13]),(0,[z1,z113,z2,z3,z4,z5,z13]),(0,[z54,z1,z2,z3,z4,z71,z13]),(0,[z1,z2,z3,z4,z5,z525,z13])],[(0,[z1,z2,z3,z526,z4,z5,z13]),(0,[z9,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z527,z13]),(0,[z1,z2,z3,z4,z528,z5,z13]),(0,[z1,z2,z3,z4,z5,z529,z13]),(0,[z44,z1,z128,z2,z3,z5,z13])],[(0,[z1,z2,z530,z3,z4,z5,z13]),(1,[z46,z2,z47,z4,z5,z13])],[(0,[z531,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z532,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z87]),(1,[z1,z2,z3,z4,z355,z5]),(0,[z1,z2,z3,z4,z5,z17,z25]),(0,[z1,z2,z3,z90,z4,z75,z13])],[(0,[z533,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z534,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z535])],[(0,[z1,z2,z536,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z5,z404]),(0,[z1,z2,z3,z4,z537,z5,z13]),(0,[z1,z157,z2,z3,z4,z5,z317]),(0,[z1,z128,z3,z23,z4,z5,z13]),(1,[z1,z53,z3,z4,z71,z13]),(0,[z1,z2,z3,z4,z538,z5,z13]),(0,[z1,z134,z2,z3,z4,z45,z5]),(0,[z1,z539,z2,z3,z4,z5,z13]),(0,[z540,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z13,z541]),(0,[z1,z2,z3,z542,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z543,z13]),(0,[z61,z1,z2,z3,z4,z5,z319]),(0,[z1,z2,z3,z4,z5,z71,z13]),(0,[z1,z2,z3,z4,z544,z5,z13])]],
   [[(0,[z1,z2,z545,z3,z4,z5,z13]),(0,[z1,z2,z3,z350,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z371,z13]),(0,[z1,z2,z3,z4,z114,z5,z13]),(0,[z546,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z23,z64,z5,z13]),(0,[z15,z1,z2,z142,z4,z5,z13]),(0,[z1,z2,z3,z547,z4,z5,z13])],[(0,[z1,z2,z3,z4,z548,z5,z13]),(0,[z549,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z550,z5,z13])],[(0,[z1,z2,z3,z4,z5,z8,z57]),(0,[z1,z134,z2,z3,z39,z4,z5]),(0,[z1,z2,z3,z90,z4,z91,z13])],[(1,[z1,z2,z3,z4,z5,z465]),(0,[z1,z2,z47,z3,z4,z5,z13]),(0,[z110,z43,z1,z2,z3,z4,z5]),(0,[z73,z1,z2,z3,z4,z5,z234]),(0,[z1,z2,z3,z551,z4,z5,z13])],[(0,[z1,z2,z3,z242,z4,z5,z13]),(0,[z54,z1,z2,z3,z4,z55,z13]),(0,[z1,z2,z3,z64,z5,z25,z13]),(0,[z552,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z553,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z485]),(0,[z554,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z555,z4,z5,z13]),(1,[z1,z2,z142,z4,z75,z13]),(0,[z15,z1,z2,z3,z4,z5,z151]),(1,[z1,z2,z3,z4,z13,z94])],[(0,[z1,z2,z3,z4,z556,z5,z13]),(0,[z107,z1,z2,z3,z4,z5,z96]),(0,[z110,z1,z2,z3,z4,z5,z7]),(0,[z1,z2,z3,z4,z5,z13,z137]),(0,[z1,z2,z3,z4,z5,z557,z13])]],
   [[(0,[z63,z1,z103,z3,z4,z5,z13]),(0,[z1,z11,z12,z3,z4,z5,z13]),(0,[z1,z2,z558,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z559,z5,z13]),(0,[z1,z560,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z561,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z8]),(0,[z562,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z45,z5,z7]),(0,[z1,z2,z3,z563,z4,z5,z13])],[(0,[z105,z1,z2,z47,z4,z5,z13]),(0,[z1,z2,z3,z4,z564,z5,z13]),(0,[z1,z565,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z566])],[(0,[z567,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z28,z5,z13]),(0,[z568,z1,z2,z3,z4,z5,z13]),(0,[z569,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z39,z4,z75,z13]),(0,[z1,z2,z3,z4,z5,z13,z151]),(0,[z162,z1,z2,z3,z152,z5,z13]),(0,[z1,z570,z2,z3,z4,z5,z13])],[(1,[z33,z1,z2,z3,z5,z13]),(0,[z1,z359,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z571,z13]),(0,[z44,z1,z2,z3,z4,z150,z13]),(0,[z1,z2,z3,z572,z4,z5,z13])],[(0,[z1,z2,z3,z573,z4,z5,z13]),(0,[z1,z2,z574,z3,z4,z5,z13]),(0,[z575,z1,z2,z3,z4,z5,z13]),(0,[z576,z1,z2,z3,z4,z5,z13])],[],[(0,[z577,z1,z2,z3,z4,z5,z13]),(0,[z105,z1,z203,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z578,z13]),(0,[z1,z2,z579,z3,z4,z5,z13])]],
   [[(0,[z1,z2,z3,z4,z580,z5,z13]),(0,[z581,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z582,z13]),(0,[z1,z2,z3,z4,z5,z583,z13]),(1,[z1,z2,z3,z4,z5,z173]),(0,[z9,z1,z2,z3,z4,z45,z5]),(0,[z1,z2,z3,z4,z584,z5,z13]),(0,[z15,z1,z2,z3,z4,z16,z13]),(0,[z1,z2,z585,z3,z4,z5,z13])],[(0,[z586,z1,z2,z3,z4,z5,z13]),(0,[z1,z587,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z588,z5,z13]),(0,[z1,z2,z3,z115,z4,z186,z13])],[(0,[z1,z2,z3,z589,z4,z5,z13]),(0,[z73,z1,z2,z3,z4,z445,z13]),(0,[z1,z2,z3,z4,z5,z590,z13]),(0,[z1,z2,z3,z4,z591,z5,z13]),(0,[z1,z2,z3,z4,z5,z75,z13]),(0,[z1,z592,z2,z3,z4,z5,z13])],[(0,[z73,z1,z2,z3,z4,z277,z13]),(0,[z1,z2,z3,z4,z5,z13,z593]),(0,[z1,z2,z3,z4,z5,z13,z69])],[(0,[z0,z1,z2,z3,z150,z5,z13]),(0,[z594,z1,z2,z3,z4,z5,z13]),(0,[z595,z1,z2,z3,z4,z5,z13])],[(0,[z9,z1,z2,z3,z39,z4,z5])],[(0,[z1,z2,z3,z4,z5,z8,z68]),(0,[z1,z2,z377,z3,z4,z5,z13]),(0,[z596,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z597,z4,z5,z13])]],
   [[(1,[z1,z2,z3,z4,z5,z339]),(0,[z1,z2,z3,z4,z150,z5,z137]),(0,[z1,z2,z598,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z599])],[(0,[z600,z1,z2,z3,z4,z5,z13]),(0,[z1,z128,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z601,z4,z5,z13]),(0,[z1,z2,z3,z4,z602,z5,z13]),(0,[z1,z2,z603,z3,z4,z5,z13]),(1,[z1,z2,z377,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z17,z13]),(0,[z1,z2,z3,z4,z604,z5,z13]),(0,[z1,z2,z3,z5,z25,z13,z80]),(0,[z1,z2,z3,z4,z605,z5,z13]),(0,[z1,z2,z3,z4,z45,z67,z13])],[(0,[z1,z606,z2,z3,z4,z5,z13]),(0,[z607,z1,z2,z3,z4,z5,z13])],[(0,[z105,z46,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z318,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z80]),(0,[z1,z2,z3,z4,z5,z608,z13])],[(0,[z2,z47,z3,z78,z4,z5,z13]),(0,[z1,z2,z3,z4,z609,z5,z13]),(0,[z1,z2,z3,z4,z5,z17,z57]),(0,[z162,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z610,z5,z13]),(0,[z121,z1,z2,z3,z64,z5,z13]),(0,[z611,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z612,z4,z5,z13])],[(0,[z613,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z614]),(0,[z1,z2,z3,z4,z5,z96,z13]),(0,[z1,z2,z3,z4,z5,z13,z615]),(0,[z1,z2,z3,z616,z4,z5,z13]),(0,[z1,z617,z2,z3,z4,z5,z13])]],
   [[(0,[z1,z2,z3,z618,z4,z5,z13]),(0,[z38,z1,z2,z3,z4,z34,z13]),(0,[z619,z1,z2,z3,z4,z5,z13]),(0,[z162,z1,z2,z3,z4,z5,z57])],[(0,[z620,z1,z2,z3,z4,z5,z13]),(0,[z157,z2,z103,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z621,z5,z13]),(0,[z1,z2,z3,z4,z355,z5,z71]),(0,[z107,z1,z2,z3,z4,z5,z17])],[(0,[z27,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z96,z57]),(0,[z1,z622,z2,z3,z4,z5,z13]),(0,[z623,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z624]),(0,[z1,z2,z3,z4,z5,z400,z13]),(0,[z1,z2,z3,z625,z4,z5,z13])],[(0,[z626,z1,z2,z3,z4,z5,z13]),(0,[z105,z73,z1,z2,z4,z5,z13]),(0,[z627,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z67,z8]),(1,[z61,z1,z3,z186,z5,z13]),(0,[z1,z2,z628,z3,z4,z5,z13]),(0,[z629,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z630,z3,z4,z5,z13]),(0,[z631,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z632,z4,z5,z13]),(0,[z1,z633,z2,z3,z4,z5,z13])],[(0,[z634,z1,z2,z3,z4,z5,z13]),(0,[z635,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z5,z74]),(0,[z1,z636,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z637,z13]),(0,[z1,z2,z3,z4,z5,z638,z13]),(0,[z1,z2,z3,z4,z639,z5,z13])],[(0,[z1,z640,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z52,z64,z5,z13]),(0,[z1,z2,z3,z4,z55,z75,z13]),(0,[z1,z2,z3,z4,z5,z56,z68]),(0,[z1,z2,z3,z22,z5,z25,z13]),(0,[z1,z2,z3,z210,z4,z5,z13])],[(1,[z1,z2,z3,z4,z5,z485]),(0,[z1,z2,z3,z641,z4,z5,z13])],[(0,[z54,z44,z1,z2,z3,z4,z13]),(0,[z121,z1,z2,z4,z64,z5,z13]),(0,[z1,z2,z3,z4,z5,z642,z13])]],
   [[(0,[z1,z643,z2,z3,z4,z5,z13]),(0,[z1,z2,z188,z3,z4,z186,z13]),(0,[z1,z2,z3,z4,z5,z644,z13]),(0,[z1,z2,z3,z4,z645,z5,z13]),(0,[z1,z2,z286,z3,z4,z349,z13])],[(0,[z1,z2,z3,z78,z4,z5,z13]),(0,[z43,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z646,z3,z4,z5,z13]),(1,[z1,z2,z136,z4,z5,z57])],[(0,[z1,z2,z647,z3,z4,z5,z13])],[(0,[z1,z2,z3,z648,z4,z5,z13]),(0,[z0,z1,z2,z3,z114,z5,z13]),(1,[z304,z2,z3,z4,z5,z13]),(0,[z649,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z409,z13]),(0,[z650,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z651,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z652])],[(0,[z1,z2,z3,z4,z5,z653,z13]),(0,[z73,z1,z2,z242,z4,z5,z13]),(0,[z107,z110,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z101,z13])],[(1,[z63,z157,z3,z4,z5,z13]),(0,[z1,z2,z3,z114,z64,z5,z13]),(0,[z1,z53,z3,z4,z5,z71,z13])],[(0,[z63,z1,z2,z3,z4,z5,z404]),(0,[z46,z1,z11,z2,z4,z5,z13]),(0,[z654,z1,z2,z3,z4,z5,z13])]],
   [[(0,[z43,z2,z3,z4,z5,z13,z8]),(0,[z655,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z142,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z656,z13])],[(0,[z1,z2,z3,z4,z5,z13,z657]),(0,[z658,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z17,z68]),(0,[z44,z1,z2,z3,z4,z16,z13])],[(1,[z104,z1,z2,z4,z5,z13]),(0,[z659,z1,z2,z3,z4,z5,z13]),(0,[z660,z1,z2,z3,z4,z5,z13]),(1,[z1,z2,z3,z4,z5,z227]),(0,[z1,z2,z3,z4,z5,z13,z260])],[(0,[z1,z2,z3,z4,z5,z13,z661]),(0,[z107,z1,z134,z3,z4,z5,z13]),(0,[z1,z2,z662,z3,z4,z5,z13]),(0,[z1,z2,z3,z90,z4,z150,z13])],[(0,[z104,z1,z2,z103,z4,z5,z13]),(0,[z105,z1,z2,z3,z4,z5,z13]),(0,[z46,z2,z47,z3,z4,z5,z13]),(0,[z51,z1,z2,z3,z4,z5,z13]),(0,[z107,z1,z2,z3,z4,z5,z13]),(0,[z1,z134,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z452,z4,z5,z13])],[(0,[z63,z1,z2,z3,z4,z5,z465]),(0,[z1,z2,z3,z601,z4,z5,z34]),(1,[z27,z2,z3,z4,z28,z13]),(0,[z1,z2,z3,z4,z5,z663,z13]),(1,[z1,z2,z3,z4,z5,z403])],[(0,[z664,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z96,z68]),(0,[z1,z2,z3,z4,z5,z665,z13]),(0,[z1,z2,z3,z4,z5,z13,z666]),(0,[z1,z2,z286,z4,z5,z75,z13]),(0,[z1,z667,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z25,z8]),(0,[z668,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z669,z5,z13]),(0,[z1,z2,z670,z3,z4,z5,z13]),(0,[z671,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z101,z25,z13])]],
   [[(1,[z102,z103,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z672,z5,z13]),(0,[z1,z2,z673,z3,z4,z5,z13]),(0,[z44,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z10,z150,z5,z13]),(0,[z110,z1,z2,z3,z10,z5,z13])],[(0,[z674,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z675,z13]),(0,[z1,z2,z3,z4,z5,z13,z676]),(0,[z1,z2,z3,z4,z5,z677,z13])],[(0,[z1,z2,z3,z4,z678,z5,z13]),(0,[z1,z2,z3,z679,z4,z5,z13])],[(0,[z1,z2,z3,z4,z45,z5,z25])],[(0,[z1,z2,z3,z4,z680,z5,z13]),(0,[z1,z2,z3,z4,z5,z681,z13])],[(1,[z1,z2,z3,z4,z5,z13]),(0,[z682,z1,z2,z3,z4,z5,z13]),(0,[z38,z1,z2,z3,z90,z4,z13]),(0,[z43,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z319,z13])],[(1,[z1,z2,z3,z231,z5,z13]),(1,[z73,z1,z242,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z191,z13]),(0,[z1,z53,z2,z3,z90,z4,z13]),(0,[z1,z683,z2,z3,z4,z5,z13])],[(0,[z38,z1,z2,z3,z4,z28,z13]),(0,[z1,z2,z684,z3,z4,z5,z13]),(0,[z1,z2,z4,z64,z5,z75,z13]),(1,[z1,z2,z3,z268,z5,z13]),(0,[z1,z2,z3,z4,z685,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z94])]],
   [[(0,[z1,z2,z3,z4,z5,z234,z13]),(1,[z1,z2,z3,z370,z4,z5]),(0,[z1,z2,z3,z4,z18,z5,z13]),(0,[z1,z2,z686,z3,z4,z5,z13])],[(1,[z105,z2,z78,z4,z5,z13]),(0,[z1,z2,z687,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z688,z5,z13])],[(1,[z1,z2,z3,z601,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z80]),(0,[z1,z2,z286,z3,z4,z5,z141]),(0,[z1,z2,z689,z3,z4,z5,z13]),(1,[z110,z1,z2,z3,z5,z80])],[(0,[z1,z2,z3,z690,z4,z5,z13]),(0,[z1,z3,z23,z4,z186,z5,z13]),(0,[z691,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z692,z4,z5,z13]),(0,[z693,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z171,z5,z13]),(0,[z694,z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z695,z3,z4,z5,z13]),(0,[z696,z1,z2,z3,z4,z5,z13]),(0,[z697,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z136,z3,z4,z5,z7]),(0,[z698,z1,z2,z3,z4,z5,z13])],[(0,[z699,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z317]),(0,[z1,z2,z3,z4,z5,z700,z13]),(0,[z701,z1,z2,z3,z4,z5,z13])],[(0,[z9,z2,z3,z4,z5,z96,z13]),(1,[z1,z2,z188,z3,z4,z13]),(0,[z1,z2,z3,z4,z5,z702,z13])],[(0,[z1,z2,z3,z703,z4,z5,z13]),(0,[z1,z2,z3,z4,z704,z5,z13]),(0,[z9,z1,z2,z3,z4,z5,z56]),(0,[z705,z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z186,z64,z5,z13]),(0,[z1,z2,z3,z4,z5,z706,z13])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z104,z1,z11,z4,z5,z13]),(0,[z1,z2,z707,z3,z4,z5]),(0,[z708,z1,z2,z3,z5,z13]),(0,[z709,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z710,z5,z13]),(0,[z1,z2,z3,z711,z4,z13]),(0,[z1,z2,z3,z4,z712,z13]),(0,[z117,z1,z2,z3,z5,z80])],[(0,[z1,z713,z3,z4,z5,z13]),(0,[z1,z714,z3,z4,z5,z13]),(0,[z61,z1,z3,z186,z5,z13]),(0,[z121,z1,z2,z64,z5,z13]),(0,[z1,z2,z3,z4,z715,z13])],[(0,[z38,z2,z3,z4,z34,z173]),(0,[z1,z2,z3,z716,z5,z13])],[(0,[z1,z11,z477,z4,z5,z13]),(0,[z1,z2,z3,z717,z5,z13]),(0,[z1,z113,z2,z3,z64,z5]),(0,[z718,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z4,z719,z13]),(0,[z44,z1,z2,z3,z580,z13]),(0,[z1,z2,z3,z4,z5,z720])],[(0,[z112,z103,z3,z4,z5,z13]),(0,[z2,z3,z721,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z485]),(0,[z1,z2,z3,z4,z722,z13]),(0,[z1,z2,z3,z723,z5,z13])],[(0,[z1,z2,z3,z4,z5,z724]),(0,[z1,z3,z4,z725,z5,z13]),(0,[z1,z2,z3,z177,z5,z25]),(0,[z1,z2,z3,z64,z5,z403]),(0,[z1,z2,z3,z4,z5,z137]),(0,[z1,z2,z3,z10,z101,z25])],[(0,[z1,z2,z3,z4,z5,z726]),(0,[z1,z2,z3,z4,z5,z727]),(0,[z1,z2,z188,z3,z22,z13]),(0,[z1,z728,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z729]),(0,[z1,z2,z3,z39,z4,z479])]],
   [[(0,[z1,z2,z3,z106,z5,z13]),(0,[z696,z1,z2,z4,z16,z13])],[(0,[z1,z203,z3,z225,z5,z13]),(0,[z1,z730,z3,z4,z5,z13]),(0,[z1,z2,z3,z731,z5,z13])],[(0,[z304,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z732,z5,z13]),(0,[z1,z2,z3,z152,z5,z13]),(0,[z1,z2,z3,z733,z5,z13]),(0,[z1,z2,z3,z22,z171,z13]),(0,[z1,z2,z3,z4,z5,z151])],[(0,[z1,z2,z3,z4,z371,z206]),(0,[z304,z2,z3,z231,z5,z13]),(0,[z2,z3,z4,z5,z734,z13]),(0,[z1,z2,z3,z10,z5,z706])],[(0,[z105,z2,z78,z106,z5,z13]),(0,[z1,z2,z3,z4,z226,z206]),(0,[z1,z2,z3,z268,z5,z151])],[(0,[z63,z157,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z1,z2,z3,z4,z5,z736]),(0,[z1,z2,z3,z4,z16,z409]),(0,[z1,z2,z3,z152,z5,z57])],[(0,[z737,z1,z2,z4,z5,z13]),(0,[z649,z2,z3,z4,z5,z8]),(0,[z107,z1,z3,z4,z5,z738]),(0,[z1,z2,z3,z4,z171,z13]),(0,[z1,z2,z3,z4,z739,z13])],[(0,[z576,z2,z3,z114,z5,z13]),(0,[z1,z2,z740,z3,z4,z13]),(0,[z360,z44,z1,z2,z3,z13]),(0,[z1,z2,z3,z39,z4,z68])]],
   [[(0,[z51,z2,z3,z741,z5,z13]),(0,[z1,z2,z3,z4,z742,z5]),(0,[z1,z2,z3,z4,z5,z743]),(0,[z1,z2,z4,z744,z5,z13])],[(0,[z745,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z746,z4,z13]),(0,[z1,z2,z3,z4,z5,z747])],[(0,[z46,z2,z341,z4,z5,z13]),(0,[z1,z134,z3,z4,z5,z738]),(0,[z1,z2,z493,z4,z5,z7]),(0,[z44,z1,z2,z3,z748,z13])],[(0,[z749,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z750,z4,z13]),(0,[z70,z1,z2,z3,z75,z13]),(0,[z1,z3,z4,z5,z738,z56]),(0,[z1,z2,z3,z4,z5,z738]),(0,[z1,z2,z4,z733,z5,z13])],[(0,[z1,z2,z3,z4,z751,z5]),(0,[z1,z2,z3,z4,z5,z752]),(0,[z1,z11,z12,z4,z5,z13]),(0,[z1,z2,z3,z725,z5,z13]),(0,[z1,z2,z3,z4,z5,z753]),(0,[z1,z53,z3,z97,z4,z71])],[(0,[z1,z2,z3,z754,z4,z5]),(0,[z1,z3,z4,z755,z5,z13]),(0,[z1,z2,z3,z756,z5,z13]),(0,[z1,z2,z3,z757,z5,z13]),(0,[z15,z1,z2,z4,z16,z151])],[(0,[z1,z2,z3,z152,z18,z13])],[(0,[z102,z103,z3,z4,z5,z13]),(0,[z104,z359,z2,z4,z5,z13]),(0,[z1,z2,z3,z49,z5,z25]),(0,[z1,z2,z3,z4,z5,z758]),(0,[z1,z2,z3,z5,z13,z759])]],
   [[(0,[z1,z2,z3,z4,z760,z13]),(0,[z1,z203,z3,z4,z5,z206]),(0,[z1,z2,z3,z4,z5,z761]),(0,[z1,z53,z3,z182,z71,z13]),(0,[z1,z2,z3,z97,z182,z5])],[(0,[z1,z2,z762,z4,z5,z13]),(0,[z102,z763,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z764,z13]),(0,[z1,z2,z3,z4,z56,z94]),(0,[z44,z1,z2,z3,z512,z13]),(0,[z110,z1,z2,z3,z5,z69]),(0,[z1,z2,z3,z45,z5,z69])],[(0,[z1,z2,z3,z4,z5,z765]),(0,[z1,z2,z3,z4,z5,z131]),(0,[z162,z1,z2,z4,z400,z7])],[(0,[z1,z2,z3,z5,z766,z13]),(0,[z46,z359,z2,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z767]),(0,[z1,z2,z768,z4,z5,z13]),(0,[z1,z2,z3,z4,z769,z13]),(0,[z1,z2,z687,z4,z5,z57]),(0,[z1,z2,z3,z4,z366,z67]),(1,[z1,z2,z4,z744,z13]),(0,[z1,z2,z3,z163,z400,z13]),(0,[z1,z2,z770,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z771]),(0,[z1,z2,z3,z772,z4,z5])],[(0,[z181,z103,z3,z4,z5,z13]),(0,[z1,z2,z3,z231,z5,z13]),(0,[z1,z2,z3,z210,z75,z13]),(0,[z110,z1,z2,z3,z5,z599])],[(0,[z105,z2,z78,z4,z5,z131]),(0,[z1,z2,z3,z773,z4,z5])],[(0,[z248,z157,z3,z4,z5,z13]),(0,[z27,z2,z3,z4,z774,z13]),(0,[z1,z155,z3,z4,z71,z13]),(0,[z1,z2,z3,z4,z5,z775])]],
   [[(0,[z2,z3,z4,z776,z5,z13]),(0,[z1,z3,z4,z777,z71,z13])],[(0,[z778,z1,z2,z4,z5,z13]),(0,[z1,z2,z3,z4,z779,z13]),(0,[z1,z2,z3,z4,z780,z5]),(0,[z110,z1,z2,z3,z5,z80])],[(0,[z1,z2,z3,z781,z5,z13]),(0,[z1,z2,z3,z4,z5,z782]),(0,[z1,z2,z3,z783,z5,z13])],[(0,[z1,z3,z4,z784,z5,z13]),(0,[z180,z2,z3,z4,z34,z13]),(0,[z73,z359,z242,z4,z5,z13]),(0,[z1,z2,z3,z785,z5,z13]),(0,[z1,z2,z3,z4,z786,z5])],[(0,[z1,z2,z3,z32,z318,z5]),(0,[z1,z2,z3,z35,z5,z234]),(0,[z70,z1,z53,z3,z71,z13]),(0,[z1,z2,z3,z787,z5,z13])],[(0,[z1,z2,z3,z4,z788,z13]),(0,[z1,z2,z3,z4,z13,z789]),(0,[z1,z2,z188,z3,z4,z13]),(0,[z1,z134,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z17,z94])],[(0,[z1,z2,z3,z790,z5,z13]),(0,[z1,z2,z3,z4,z791,z13]),(0,[z1,z2,z3,z792,z5,z13]),(0,[z1,z2,z793,z4,z5,z13])],[(0,[z1,z2,z3,z4,z794,z13]),(0,[z1,z2,z3,z4,z795,z13]),(0,[z1,z2,z3,z4,z796,z13]),(0,[z1,z2,z3,z797,z4,z5]),(0,[z1,z2,z286,z22,z349,z13])]],
   [[(0,[z1,z2,z3,z798,z5,z13])],[(0,[z1,z2,z3,z4,z5,z799]),(0,[z1,z134,z3,z4,z5,z543]),(0,[z73,z1,z242,z4,z5,z234]),(0,[z1,z3,z800,z4,z5,z13]),(0,[z1,z2,z144,z350,z5,z13])],[(0,[z1,z2,z3,z4,z5,z801]),(0,[z61,z1,z3,z186,z5,z319]),(0,[z1,z2,z3,z115,z4,z13]),(0,[z1,z2,z3,z4,z5,z802])],[(0,[z1,z216,z3,z4,z5,z13]),(0,[z0,z2,z3,z114,z5,z13]),(0,[z1,z2,z3,z803,z4,z13]),(0,[z70,z1,z53,z2,z3,z13]),(0,[z1,z2,z3,z4,z224,z67])],[(0,[z27,z33,z1,z2,z3,z13]),(0,[z73,z304,z242,z4,z5,z13]),(0,[z1,z2,z3,z4,z804,z13]),(0,[z311,z1,z3,z4,z55,z13]),(0,[z1,z2,z4,z171,z75,z13])],[(0,[z1,z2,z805,z4,z5,z13]),(0,[z1,z2,z3,z4,z32,z5]),(0,[z806,z2,z3,z4,z5,z13]),(0,[z807,z2,z3,z4,z5,z13]),(0,[z1,z2,z257,z4,z5,z57])],[(0,[z808,z1,z2,z3,z5,z13]),(0,[z2,z3,z4,z809,z5,z13]),(0,[z810,z1,z2,z3,z4,z5]),(0,[z44,z1,z2,z3,z393,z13])],[(0,[z105,z216,z78,z4,z5,z13]),(0,[z38,z2,z3,z4,z34,z13]),(1,[z2,z3,z4,z774,z13]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z1,z2,z3,z4,z5,z812]),(0,[z1,z53,z3,z4,z777,z13])]],
   [[(0,[z1,z2,z3,z5,z13,z813])],[(0,[z1,z2,z3,z4,z814,z5]),(0,[z1,z2,z3,z4,z815,z5]),(0,[z1,z2,z3,z4,z5,z260]),(0,[z1,z2,z3,z5,z748,z13]),(1,[z1,z2,z3,z5,z816])],[(0,[z1,z2,z3,z4,z5,z817]),(0,[z1,z12,z800,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z2,z136,z4,z5,z819])],[(0,[z46,z2,z721,z4,z5,z13]),(1,[z2,z3,z4,z5,z820]),(0,[z43,z2,z3,z4,z5,z820]),(0,[z1,z2,z3,z821,z4,z5]),(0,[z1,z2,z3,z4,z822,z13])],[(0,[z1,z2,z3,z35,z277,z13]),(0,[z1,z2,z3,z4,z5,z823])],[(0,[z1,z2,z824,z4,z5,z13]),(0,[z63,z157,z3,z4,z5,z317]),(0,[z203,z3,z78,z4,z5,z13]),(0,[z1,z2,z3,z4,z825,z13]),(0,[z9,z2,z3,z4,z605,z5]),(0,[z70,z1,z2,z3,z355,z5]),(0,[z1,z2,z3,z148,z5,z80])],[(0,[z1,z2,z3,z4,z826,z13]),(0,[z1,z2,z3,z827,z5,z13]),(0,[z1,z2,z3,z828,z5,z13]),(0,[z1,z2,z3,z39,z4,z270])],[(0,[z2,z3,z4,z5,z820,z8]),(0,[z829,z1,z2,z3,z4,z5]),(0,[z61,z1,z377,z3,z186,z5]),(0,[z162,z1,z2,z4,z18,z7])]],
   [[(0,[z1,z53,z689,z3,z4,z13]),(0,[z1,z2,z3,z163,z18,z13])],[(0,[z1,z2,z3,z4,z5,z830])],[(0,[z1,z11,z203,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z831]),(0,[z54,z1,z3,z4,z55,z13])],[(0,[z1,z2,z3,z4,z5,z832]),(0,[z2,z721,z78,z4,z5,z13]),(0,[z33,z38,z1,z2,z3,z13])],[(0,[z833,z1,z2,z3,z4,z13]),(0,[z1,z2,z3,z4,z5,z834]),(0,[z1,z2,z3,z835,z4,z5]),(0,[z359,z2,z3,z4,z5,z74]),(0,[z1,z2,z377,z3,z64,z5]),(0,[z1,z2,z3,z836,z4,z5]),(0,[z1,z53,z3,z4,z355,z71]),(0,[z1,z2,z3,z4,z5,z837]),(0,[z1,z2,z3,z4,z45,z67])],[(1,[z1,z3,z4,z777,z13]),(0,[z1,z2,z3,z39,z4,z615])],[(0,[z1,z2,z3,z838,z5,z13]),(0,[z1,z2,z3,z4,z5,z839]),(0,[z44,z1,z2,z3,z91,z13])],[(0,[z1,z203,z3,z4,z371,z13]),(0,[z46,z2,z673,z4,z5,z13]),(0,[z1,z201,z2,z3,z22,z13]),(0,[z2,z3,z4,z774,z34,z13]),(0,[z1,z2,z3,z4,z349,z161]),(0,[z1,z2,z840,z4,z5,z13])]],
   [[(0,[z1,z2,z3,z841,z5,z13]),(0,[z1,z2,z3,z842,z4,z5]),(0,[z1,z2,z3,z39,z4,z624]),(0,[z1,z843,z3,z4,z5,z13])],[(0,[z43,z299,z2,z3,z4,z5]),(0,[z1,z2,z286,z22,z5,z141]),(0,[z1,z2,z3,z5,z13,z816])],[(0,[z1,z2,z3,z4,z5,z844]),(0,[z1,z2,z3,z4,z5,z845]),(0,[z846,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z10,z559,z5]),(0,[z44,z1,z2,z3,z440,z13])],[(0,[z1,z2,z4,z847,z5,z13]),(0,[z1,z2,z3,z64,z171,z13]),(0,[z1,z2,z3,z10,z5,z480])],[(0,[z1,z2,z3,z4,z5,z317]),(0,[z1,z2,z3,z4,z5,z319]),(0,[z848,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z849,z13]),(0,[z33,z1,z2,z3,z75,z13]),(0,[z202,z2,z3,z4,z5,z96]),(0,[z1,z2,z144,z22,z5,z13])],[(0,[z1,z2,z3,z5,z13,z850])],[(0,[z851,z1,z2,z3,z4,z5]),(0,[z517,z44,z1,z2,z3,z13]),(0,[z44,z540,z1,z2,z3,z13]),(0,[z1,z2,z3,z5,z403,z69])]],
   [[(0,[z1,z2,z3,z852,z5,z13]),(0,[z33,z1,z2,z3,z601,z5])],[(0,[z1,z2,z3,z106,z5,z131]),(0,[z1,z2,z3,z853,z5,z13]),(0,[z1,z2,z3,z854,z5,z13]),(0,[z1,z2,z500,z4,z75,z13])],[(0,[z104,z1,z2,z855,z5,z13]),(0,[z1,z856,z3,z4,z5,z13])],[(0,[z1,z2,z721,z4,z5,z13]),(0,[z0,z2,z3,z741,z5,z13]),(0,[z2,z3,z4,z5,z820,z13]),(0,[z1,z2,z3,z402,z4,z68])],[(0,[z1,z2,z3,z4,z857,z13]),(0,[z1,z2,z158,z22,z5,z13])],[(0,[z1,z3,z4,z5,z858,z13]),(0,[z9,z2,z3,z4,z5,z820])],[(0,[z1,z2,z3,z4,z5,z859]),(0,[z1,z2,z3,z4,z5,z860]),(0,[z861,z1,z2,z3,z5,z13])],[(0,[z1,z2,z3,z4,z5,z862]),(0,[z1,z2,z3,z863,z5,z13]),(0,[z1,z2,z3,z864,z4,z5]),(0,[z1,z2,z3,z5,z403,z80])]],
   [[(0,[z1,z2,z3,z4,z865,z13]),(0,[z1,z128,z3,z519,z5,z13]),(0,[z1,z2,z3,z866,z5,z13])],[(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z2,z3,z868,z4,z5]),(0,[z359,z2,z3,z35,z5,z13]),(0,[z1,z2,z3,z4,z869,z13]),(0,[z1,z2,z3,z4,z349,z13]),(0,[z1,z2,z3,z4,z748,z13])],[(0,[z298,z1,z2,z4,z5,z7]),(0,[z1,z2,z3,z4,z18,z7])],[(1,[z763,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z870]),(0,[z1,z2,z3,z4,z45,z830])],[(0,[z1,z2,z3,z4,z871,z5]),(0,[z1,z2,z3,z4,z5,z872]),(0,[z1,z2,z3,z873,z4,z5])],[(0,[z103,z3,z145,z4,z5,z13]),(0,[z359,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z855,z5,z13]),(0,[z44,z1,z2,z3,z497,z13])],[(0,[z359,z2,z3,z231,z5,z13]),(0,[z1,z2,z3,z97,z4,z16]),(0,[z1,z2,z3,z350,z75,z13])],[(0,[z0,z2,z3,z114,z5,z485]),(0,[z1,z2,z3,z874,z4,z5]),(0,[z1,z2,z3,z182,z5,z13])]],
   [[(0,[z763,z103,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z875]),(0,[z1,z2,z3,z4,z233,z68]),(0,[z1,z2,z3,z4,z45,z94]),(0,[z1,z2,z3,z39,z4,z830])],[(0,[z102,z31,z103,z4,z5,z13]),(0,[z104,z2,z78,z4,z5,z13]),(0,[z1,z2,z3,z4,z876,z13]),(0,[z38,z2,z3,z4,z774,z13]),(0,[z1,z2,z3,z877,z5,z13]),(0,[z304,z2,z3,z4,z5,z234]),(1,[z1,z3,z4,z5,z738]),(0,[z1,z134,z3,z612,z4,z5]),(0,[z1,z2,z3,z10,z5,z25])],[(0,[z1,z2,z3,z4,z878,z13]),(0,[z1,z216,z3,z106,z5,z13]),(0,[z1,z2,z3,z4,z5,z879]),(0,[z1,z2,z3,z150,z5,z485]),(0,[z1,z2,z880,z3,z4,z5]),(0,[z1,z2,z3,z4,z881,z13]),(0,[z1,z2,z3,z601,z4,z75]),(0,[z1,z2,z3,z4,z5,z882]),(1,[z1,z3,z725,z5,z13]),(0,[z883,z1,z2,z3,z4,z13]),(0,[z1,z2,z286,z22,z5,z161]),(0,[z44,z1,z2,z144,z91,z13])],[(0,[z1,z2,z3,z884,z4,z13]),(0,[z1,z2,z4,z5,z7,z819]),(0,[z1,z2,z3,z4,z885,z13])],[(0,[z1,z2,z3,z4,z886,z13]),(0,[z104,z102,z103,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z887]),(0,[z1,z2,z3,z4,z888,z13]),(0,[z1,z2,z3,z4,z5,z889]),(0,[z44,z1,z2,z3,z515,z13])],[(0,[z1,z2,z3,z890,z4,z13]),(0,[z1,z201,z2,z3,z4,z13]),(0,[z1,z2,z3,z4,z891,z13]),(0,[z61,z1,z3,z370,z186,z5]),(0,[z1,z2,z3,z4,z5,z892]),(0,[z1,z2,z3,z90,z150,z403]),(0,[z1,z2,z3,z39,z4,z94])],[(0,[z1,z2,z3,z4,z893,z13]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z1,z2,z3,z275,z395,z4]),(0,[z1,z2,z493,z22,z5,z13])],[(0,[z1,z2,z895,z4,z5,z13])]],
   [[(0,[z1,z2,z3,z4,z896,z13]),(0,[z43,z2,z3,z4,z5,z8]),(0,[z897,z1,z2,z3,z5,z13])],[(0,[z1,z2,z3,z898,z5,z13]),(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z113,z2,z3,z395,z4]),(0,[z9,z2,z3,z4,z5,z96]),(0,[z1,z2,z3,z4,z445,z74]),(0,[z54,z1,z3,z4,z453,z13])],[(0,[z1,z2,z3,z4,z277,z74]),(0,[z1,z2,z3,z4,z5,z899]),(0,[z1,z2,z3,z4,z830,z68])],[(0,[z1,z2,z3,z900,z5,z13]),(0,[z1,z901,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z902]),(0,[z1,z2,z3,z4,z16,z233]),(0,[z1,z903,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z830])],[(0,[z1,z2,z3,z741,z5,z13]),(0,[z904,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z905])],[(0,[z1,z2,z3,z4,z5,z906]),(0,[z1,z2,z3,z4,z226,z13]),(0,[z907,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z90,z150,z13])],[(0,[z1,z2,z3,z908,z5,z13]),(0,[z1,z2,z3,z150,z5,z227]),(0,[z1,z2,z3,z90,z4,z87]),(0,[z1,z2,z3,z4,z5,z909]),(0,[z1,z2,z3,z4,z5,z910])],[(0,[z1,z2,z3,z4,z5,z911]),(0,[z1,z2,z3,z281,z150,z13]),(0,[z1,z2,z3,z10,z101,z13])]],
   [[(0,[z304,z2,z3,z4,z445,z13]),(0,[z1,z2,z3,z912,z5,z13]),(0,[z1,z2,z3,z4,z5,z913]),(0,[z267,z1,z3,z186,z5,z13]),(0,[z1,z2,z188,z3,z64,z13]),(0,[z1,z2,z3,z914,z5,z13]),(0,[z44,z1,z333,z2,z3,z13])],[(0,[z105,z2,z78,z4,z226,z13]),(0,[z304,z2,z3,z4,z277,z13])],[(0,[z1,z2,z3,z4,z5,z915]),(0,[z2,z3,z4,z741,z5,z13]),(0,[z1,z2,z3,z4,z5,z233])],[(0,[z1,z461,z3,z4,z5,z17]),(0,[z189,z2,z3,z4,z5,z96]),(0,[z1,z2,z3,z4,z5,z234]),(0,[z1,z2,z3,z4,z5,z141]),(0,[z295,z1,z2,z64,z5,z13])],[(0,[z1,z216,z3,z4,z5,z131]),(0,[z1,z2,z3,z231,z5,z234]),(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z2,z3,z4,z917,z13])],[(0,[z179,z2,z3,z4,z5,z96]),(0,[z1,z2,z3,z4,z918,z13]),(0,[z1,z2,z3,z4,z45,z464])],[(0,[z1,z2,z3,z4,z5,z919]),(0,[z1,z2,z3,z920,z4,z13]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z2,z3,z4,z75,z409]),(0,[z1,z2,z3,z350,z5,z409]),(0,[z162,z1,z2,z4,z5,z7])],[(0,[z1,z2,z3,z922,z4,z5]),(0,[z1,z2,z3,z163,z5,z13]),(0,[z1,z2,z3,z10,z5,z403]),(0,[z1,z2,z3,z5,z25,z816])]],
   [[(0,[z1,z2,z3,z4,z923,z13])],[(0,[z1,z2,z3,z225,z5,z13]),(0,[z1,z2,z3,z4,z5,z132]),(0,[z924,z2,z3,z4,z5,z13]),(0,[z162,z1,z2,z4,z5,z819]),(0,[z1,z2,z3,z90,z4,z137])],[(0,[z1,z2,z3,z4,z5,z925])],[(0,[z1,z2,z3,z926,z4,z13]),(0,[z1,z2,z3,z4,z5,z927]),(0,[z44,z1,z2,z3,z571,z13])],[(0,[z104,z1,z2,z4,z928,z13]),(0,[z1,z2,z3,z4,z5,z929])],[(0,[z105,z2,z78,z225,z5,z13]),(0,[z930,z1,z2,z3,z5,z13]),(0,[z1,z2,z3,z4,z5,z931]),(0,[z932,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z933,z4,z5]),(0,[z1,z2,z3,z35,z445,z13]),(0,[z70,z1,z2,z3,z5,z13]),(0,[z1,z2,z3,z150,z13,z192])],[(0,[z1,z2,z3,z4,z934,z13]),(0,[z1,z935,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z936]),(0,[z1,z2,z937,z3,z4,z5]),(0,[z1,z2,z3,z152,z5,z7])]],
   [[(0,[z1,z2,z4,z938,z5,z13])],[(0,[z0,z201,z2,z3,z114,z13]),(0,[z33,z38,z2,z3,z34,z13]),(0,[z939,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z940]),(0,[z1,z2,z3,z4,z941,z13]),(0,[z1,z2,z3,z4,z445,z13]),(0,[z1,z2,z3,z4,z13,z942])],[(0,[z1,z2,z3,z4,z277,z13]),(0,[z1,z2,z3,z4,z943,z13]),(0,[z1,z2,z3,z231,z445,z13]),(0,[z73,z1,z242,z4,z445,z13]),(0,[z1,z2,z3,z4,z944,z13]),(0,[z1,z2,z170,z4,z75,z13])],[(0,[z1,z2,z3,z945,z4,z5]),(0,[z1,z2,z3,z39,z4,z401]),(0,[z1,z2,z3,z231,z277,z13]),(0,[z73,z1,z242,z4,z277,z13]),(0,[z1,z800,z242,z4,z5,z13])],[(0,[z1,z2,z3,z5,z8,z69])],[(0,[z1,z2,z3,z90,z391,z13]),(0,[z43,z2,z3,z4,z5,z320]),(0,[z1,z2,z144,z4,z171,z13]),(0,[z1,z2,z3,z4,z5,z946])],[(0,[z1,z2,z3,z4,z928,z13]),(0,[z1,z2,z3,z4,z5,z947]),(0,[z110,z1,z2,z3,z327,z5]),(0,[z948,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z949]),(0,[z1,z2,z3,z39,z5,z69])]],
   [[(0,[z950,z1,z2,z3,z5,z13]),(0,[z1,z2,z3,z4,z5,z206]),(0,[z1,z2,z3,z4,z5,z951]),(0,[z1,z2,z3,z22,z5,z161]),(0,[z1,z2,z3,z210,z5,z13])],[(0,[z1,z2,z3,z4,z5,z952]),(0,[z1,z2,z953,z4,z5,z13]),(0,[z51,z1,z201,z2,z3,z13]),(0,[z1,z2,z3,z4,z5,z954]),(0,[z619,z1,z2,z4,z5,z7]),(0,[z15,z1,z2,z4,z744,z13]),(0,[z1,z2,z955,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z956]),(0,[z1,z2,z3,z4,z5,z957]),(0,[z1,z2,z3,z958,z4,z5])],[(0,[z1,z2,z800,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z960,z2,z3,z4,z5,z13]),(0,[z961,z1,z2,z3,z5,z13])],[(0,[z105,z2,z78,z4,z5,z206]),(0,[z38,z2,z3,z4,z34,z132]),(0,[z1,z2,z3,z962,z5,z13]),(0,[z1,z2,z4,z16,z744,z13]),(0,[z552,z1,z2,z4,z16,z13]),(0,[z963,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z45,z233])],[(0,[z1,z2,z3,z4,z5,z964]),(0,[z1,z53,z3,z4,z71,z191]),(0,[z1,z2,z144,z4,z16,z13]),(1,[z1,z2,z3,z748,z13])],[(0,[z1,z2,z3,z4,z965,z13]),(0,[z1,z2,z3,z966,z5,z13]),(0,[z967,z1,z3,z4,z5,z13]),(1,[z1,z800,z4,z5,z13])],[(0,[z1,z2,z3,z4,z45,z706])]],
   [[(0,[z1,z2,z3,z968,z5,z13]),(0,[z1,z2,z3,z4,z969,z13]),(0,[z104,z46,z2,z4,z5,z13]),(0,[z1,z2,z3,z970,z5,z13]),(0,[z107,z1,z3,z4,z5,z269]),(0,[z1,z128,z3,z23,z5,z13])],[(0,[z2,z763,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z2,z3,z4,z5,z972]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z1,z3,z4,z5,z17,z738])],[(0,[z1,z2,z3,z4,z5,z974]),(0,[z1,z2,z3,z975,z5,z13]),(0,[z976,z2,z3,z4,z5,z13])],[(0,[z44,z1,z2,z3,z416,z13]),(0,[z1,z2,z3,z5,z816,z80])],[(0,[z1,z2,z3,z4,z5,z977]),(0,[z1,z11,z800,z4,z5,z13]),(0,[z1,z2,z144,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z819])],[(0,[z107,z1,z3,z4,z688,z5]),(0,[z1,z2,z3,z4,z5,z978])],[(0,[z1,z2,z979,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z2,z3,z981,z5,z13]),(0,[z1,z2,z3,z4,z5,z982]),(0,[z1,z592,z3,z4,z5,z56]),(0,[z1,z2,z3,z101,z13,z80])],[(0,[z1,z11,z695,z4,z5,z13]),(0,[z1,z2,z3,z983,z4,z5]),(0,[z44,z1,z2,z3,z5,z227]),(0,[z1,z617,z3,z4,z5,z56]),(0,[z629,z1,z2,z3,z5,z80]),(0,[z1,z2,z144,z4,z5,z775]),(0,[z1,z2,z3,z4,z148,z67])]],
   [[],[(0,[z0,z2,z3,z395,z114,z13]),(0,[z1,z2,z3,z4,z13,z984]),(0,[z1,z2,z3,z985,z4,z5])],[(0,[z986,z1,z2,z4,z5,z13]),(0,[z1,z2,z3,z4,z987,z13]),(0,[z1,z2,z3,z90,z150,z137])],[(0,[z1,z2,z3,z988,z5,z13]),(0,[z347,z103,z3,z4,z5,z13]),(0,[z1,z2,z3,z106,z371,z13]),(0,[z1,z2,z286,z350,z5,z13])],[(0,[z104,z1,z2,z4,z5,z989]),(0,[z1,z2,z3,z106,z226,z13]),(0,[z1,z2,z3,z4,z774,z13]),(0,[z229,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z45,z192])],[(0,[z1,z2,z3,z4,z5,z990])],[(0,[z1,z2,z3,z355,z182,z5]),(0,[z107,z1,z3,z4,z50,z5])],[(0,[z46,z2,z47,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z1,z3,z4,z777,z5,z13]),(0,[z1,z2,z3,z5,z17,z69]),(0,[z1,z2,z3,z45,z67,z69])]],
   [[(0,[z1,z2,z3,z4,z992,z13]),(0,[z1,z2,z3,z4,z5,z820]),(0,[z1,z2,z3,z4,z355,z5])],[(0,[z993,z1,z2,z3,z4,z5]),(0,[z1,z62,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z994]),(0,[z15,z1,z2,z4,z16,z409])],[(0,[z61,z1,z3,z725,z5,z13]),(0,[z1,z3,z725,z186,z5,z13]),(0,[z1,z2,z3,z692,z4,z68]),(0,[z1,z2,z144,z4,z5,z802]),(0,[z1,z2,z3,z5,z13,z69]),(0,[z1,z2,z3,z4,z510,z68]),(0,[z1,z2,z3,z210,z45,z13])],[(0,[z105,z359,z2,z4,z5,z13]),(0,[z1,z2,z3,z995,z4,z5]),(0,[z1,z2,z3,z996,z5,z13]),(0,[z1,z2,z3,z10,z5,z816])],[(0,[z1,z2,z3,z997,z5,z13]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z46,z203,z3,z4,z5,z13]),(0,[z1,z2,z3,z5,z96,z69])],[(0,[z1,z2,z3,z4,z5,z999])],[(0,[z1,z2,z3,z4,z5,z1000]),(0,[z1001,z1,z2,z3,z5,z13]),(0,[z1,z2,z3,z1002,z5,z13]),(0,[z1,z2,z3,z4,z5,z1003]),(0,[z1,z2,z3,z4,z1004,z13]),(0,[z1,z2,z3,z1005,z5,z13])],[(0,[z1,z2,z3,z4,z5,z1006]),(0,[z38,z451,z2,z3,z4,z13]),(0,[z1,z2,z188,z377,z3,z4]),(0,[z162,z1,z2,z152,z5,z7])]],
   [[(0,[z1,z203,z3,z106,z5,z13]),(0,[z1,z201,z2,z3,z64,z13]),(0,[z1,z2,z3,z1007,z4,z5]),(0,[z1,z2,z3,z4,z1008,z13]),(0,[z1,z2,z3,z4,z171,z141])],[(0,[z1,z2,z3,z4,z5,z1009]),(0,[z359,z11,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z45,z438])],[(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z2,z3,z318,z5,z13]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z1,z2,z3,z4,z5,z1012]),(0,[z1,z2,z142,z4,z75,z13])],[(1,[z2,z721,z4,z5,z13]),(0,[z1,z113,z2,z3,z22,z5]),(0,[z70,z1,z2,z3,z97,z5])],[(0,[z359,z2,z3,z4,z5,z234])],[(0,[z1,z1013,z3,z4,z5,z13]),(0,[z51,z2,z3,z52,z5,z13]),(0,[z1,z2,z3,z4,z13,z1014])],[(0,[z1,z2,z3,z4,z226,z131]),(0,[z1,z2,z3,z4,z1015,z13]),(0,[z1,z2,z3,z5,z13,z1016]),(0,[z61,z1,z188,z3,z186,z13]),(0,[z1,z539,z3,z23,z5,z13]),(0,[z1017,z1,z2,z3,z5,z13]),(0,[z1,z2,z3,z150,z748,z13])],[(0,[z63,z763,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z371,z13])]],
   [[(0,[z1,z2,z3,z4,z5,z1018]),(0,[z33,z1,z2,z3,z5,z13]),(0,[z1,z2,z3,z10,z5,z638])],[(0,[z1,z2,z3,z4,z5,z1019])],[(0,[z1,z2,z3,z39,z4,z236])],[(0,[z1,z2,z3,z4,z1020,z13]),(0,[z105,z2,z78,z4,z371,z13]),(0,[z1,z2,z3,z150,z335,z13]),(0,[z61,z1,z3,z115,z186,z13]),(0,[z489,z1,z2,z64,z5,z13])],[(0,[z1,z2,z3,z4,z1021,z13]),(0,[z1,z2,z3,z1022,z4,z5]),(0,[z190,z1,z2,z3,z5,z80]),(0,[z1,z2,z3,z4,z5,z1023]),(0,[z1,z2,z3,z1024,z5,z13]),(0,[z1,z2,z3,z24,z5,z25])],[(0,[z104,z1,z2,z1025,z5,z13]),(0,[z1,z2,z3,z4,z5,z1026]),(0,[z1,z2,z4,z744,z75,z13])],[(0,[z44,z1,z2,z3,z230,z13]),(0,[z1,z2,z3,z1027,z4,z5]),(0,[z304,z2,z3,z4,z5,z74]),(0,[z1,z2,z1028,z4,z5,z13]),(0,[z1,z2,z1029,z4,z5,z13]),(0,[z1030,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z106,z5,z206]),(0,[z1,z2,z3,z4,z5,z1031]),(0,[z1,z2,z3,z1032,z5,z13]),(0,[z1,z2,z3,z4,z5,z1033]),(0,[z1,z2,z286,z22,z5,z13])]],
   [[(0,[z1,z2,z3,z4,z1034,z13]),(0,[z110,z1,z2,z3,z5,z324]),(0,[z44,z1,z2,z3,z13,z19]),(0,[z1,z2,z3,z4,z5,z1035])],[(0,[z1,z2,z3,z1036,z5,z13]),(0,[z1,z2,z3,z4,z1037,z5]),(0,[z1,z1038,z2,z3,z4,z13]),(0,[z1,z2,z48,z4,z5,z57]),(0,[z1,z2,z3,z4,z5,z1039]),(0,[z1,z2,z3,z10,z25,z94]),(0,[z1,z2,z3,z10,z5,z69])],[(0,[z1,z2,z3,z1040,z5,z13]),(0,[z1,z2,z3,z225,z5,z131]),(0,[z1,z2,z3,z4,z5,z1041]),(0,[z1,z2,z3,z4,z1042,z13]),(0,[z44,z1,z2,z3,z4,z87]),(0,[z70,z1,z2,z3,z16,z13]),(0,[z1,z2,z3,z4,z744,z13]),(0,[z1,z2,z3,z58,z5,z25])],[(0,[z105,z2,z721,z4,z5,z13]),(0,[z0,z2,z3,z114,z5,z6]),(0,[z1,z2,z3,z97,z4,z5]),(0,[z110,z1,z2,z3,z5,z331]),(0,[z1,z2,z3,z90,z150,z233])],[(0,[z1,z203,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1043]),(0,[z1,z2,z3,z4,z5,z1044]),(0,[z1,z2,z3,z4,z5,z1045])],[(0,[z38,z2,z3,z318,z34,z13]),(0,[z1,z2,z3,z150,z362,z13]),(0,[z552,z1,z2,z4,z5,z7])],[(0,[z1,z1046,z3,z4,z5,z13]),(0,[z359,z3,z242,z4,z5,z13]),(0,[z1047,z2,z3,z4,z5,z13]),(0,[z1,z2,z377,z3,z4,z5]),(1,[z1,z2,z733,z5,z13]),(0,[z44,z1,z2,z3,z36,z13]),(0,[z1,z2,z3,z152,z400,z13])],[(0,[z1,z2,z3,z1048,z5,z13]),(0,[z1,z216,z3,z4,z226,z13]),(0,[z1,z2,z1049,z4,z5,z13])]],
   [[(0,[z1,z763,z3,z4,z5,z13]),(0,[z104,z1,z2,z4,z5,z1050]),(0,[z1,z2,z3,z1025,z5,z13]),(0,[z105,z203,z78,z4,z5,z13]),(0,[z1,z2,z3,z395,z4,z13])],[(0,[z522,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z350,z5,z13]),(0,[z1,z2,z3,z4,z171,z161])],[(0,[z1,z2,z1051,z4,z5,z13]),(0,[z73,z1,z203,z4,z5,z13]),(0,[z1,z2,z3,z225,z226,z13]),(0,[z1,z2,z3,z4,z5,z1052])],[(0,[z157,z763,z3,z4,z5,z13]),(0,[z63,z474,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1053]),(0,[z1,z2,z412,z22,z5,z13]),(0,[z1,z2,z3,z4,z5,z1054])],[(0,[z1,z2,z3,z4,z5,z1055]),(0,[z1,z2,z3,z4,z5,z1056]),(0,[z1,z2,z3,z35,z5,z74]),(0,[z1,z2,z3,z1057,z5,z13]),(0,[z271,z1,z2,z64,z5,z13]),(0,[z1,z2,z3,z4,z5,z1058]),(0,[z1,z2,z3,z210,z16,z13])],[(0,[z44,z1,z2,z3,z4,z137]),(0,[z1,z2,z3,z90,z150,z260])],[(0,[z1,z2,z3,z275,z4,z5]),(0,[z1,z2,z3,z4,z5,z1059]),(0,[z1,z2,z3,z1060,z5,z13]),(0,[z1,z2,z3,z1061,z5,z13]),(0,[z1,z2,z3,z1062,z5,z13])],[(0,[z1,z2,z3,z4,z5,z1063]),(0,[z2,z47,z721,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1064]),(0,[z1,z2,z3,z1065,z5,z13]),(0,[z1,z2,z3,z4,z5,z1066]),(0,[z1,z2,z3,z1067,z5,z13])]],
   [[(0,[z104,z1,z203,z4,z5,z13]),(0,[z1,z2,z3,z1068,z4,z5]),(0,[z1,z2,z3,z1069,z5,z13]),(0,[z1,z2,z3,z4,z5,z74]),(0,[z1,z2,z3,z4,z5,z1070]),(0,[z110,z1,z2,z3,z5,z816])],[(0,[z1,z2,z3,z4,z5,z1071]),(0,[z1,z2,z3,z4,z1072,z13]),(0,[z1,z2,z3,z1073,z5,z13]),(0,[z1,z113,z2,z3,z4,z5]),(0,[z38,z2,z3,z601,z4,z34]),(0,[z1,z2,z3,z231,z5,z74]),(0,[z73,z1,z242,z4,z5,z74]),(0,[z107,z1,z3,z4,z5,z17]),(0,[z1,z2,z144,z64,z5,z13]),(0,[z1,z2,z686,z4,z75,z13]),(0,[z162,z1,z2,z163,z5,z7]),(0,[z1,z2,z3,z90,z13,z480])],[(0,[z1,z2,z3,z4,z5,z1074]),(0,[z1,z2,z4,z1075,z5,z13]),(0,[z1,z1076,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1077]),(0,[z1,z2,z3,z4,z5,z1078]),(0,[z1,z2,z3,z1079,z4,z13])],[(0,[z1,z2,z3,z4,z5,z1050]),(0,[z1,z216,z3,z225,z5,z13]),(0,[z304,z2,z3,z35,z5,z13]),(0,[z54,z1,z3,z4,z777,z13]),(0,[z1,z2,z452,z4,z5,z13])],[(0,[z1,z2,z3,z1080,z5,z13]),(0,[z2,z3,z741,z114,z5,z13]),(0,[z2,z3,z52,z741,z5,z13]),(0,[z1,z2,z3,z601,z4,z16]),(0,[z1,z2,z3,z4,z5,z191]),(0,[z1,z2,z350,z64,z5,z13]),(0,[z1,z2,z3,z4,z75,z233]),(0,[z15,z1,z2,z350,z16,z13])],[(0,[z1,z2,z3,z22,z101,z13]),(0,[z1,z2,z136,z4,z5,z57])],[(0,[z44,z1,z2,z3,z5,z485]),(0,[z1,z266,z3,z4,z5,z56]),(0,[z1,z3,z4,z5,z738,z13]),(0,[z1,z2,z3,z4,z5,z1081]),(0,[z1,z2,z3,z90,z748,z13])],[(0,[z1,z2,z3,z4,z1082,z13]),(0,[z1,z1083,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z161])]],
   [[(0,[z1,z2,z3,z4,z8,z94]),(0,[z1,z2,z3,z4,z400,z13])],[(0,[z1,z2,z3,z4,z5,z1084]),(0,[z1,z2,z3,z4,z445,z234]),(0,[z1085,z2,z3,z4,z5,z13]),(0,[z73,z1,z800,z4,z5,z13]),(0,[z1,z2,z3,z370,z115,z4]),(0,[z1,z2,z3,z4,z101,z13]),(0,[z1,z2,z3,z150,z5,z260])],[(0,[z1,z2,z3,z4,z5,z1086]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z1,z2,z3,z4,z45,z159]),(0,[z1,z2,z3,z4,z277,z234])],[(0,[z1,z1088,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1089]),(0,[z0,z451,z2,z3,z5,z13]),(0,[z1,z2,z3,z90,z195,z13])],[(0,[z1,z2,z1090,z4,z5,z13]),(0,[z2,z3,z4,z28,z774,z13]),(0,[z9,z2,z3,z4,z5,z329]),(0,[z1,z2,z3,z4,z1091,z13]),(0,[z110,z1,z2,z3,z5,z566]),(0,[z117,z1,z2,z3,z4,z68]),(0,[z1,z2,z3,z1092,z5,z13])],[(0,[z1,z2,z3,z1093,z4,z13]),(0,[z38,z2,z3,z4,z32,z34]),(0,[z1,z2,z3,z4,z5,z1094]),(0,[z1,z2,z3,z22,z5,z403])],[(0,[z104,z1,z2,z4,z5,z13]),(0,[z63,z157,z3,z4,z5,z404]),(0,[z1,z2,z3,z4,z1095,z5]),(0,[z1,z2,z3,z4,z1096,z13]),(0,[z1,z2,z3,z4,z5,z227]),(0,[z1,z2,z3,z5,z56,z69]),(0,[z1,z2,z4,z5,z819,z13])],[]],
   [[(0,[z1,z2,z4,z1097,z5,z13]),(0,[z1,z2,z4,z5,z1098,z13]),(0,[z1,z1099,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1100]),(0,[z1101,z2,z3,z4,z5,z13])],[(0,[z1,z2,z4,z5,z1102,z13]),(0,[z1,z1103,z3,z4,z5,z13]),(0,[z27,z2,z3,z4,z28,z13]),(0,[z1,z2,z3,z4,z5,z409]),(0,[z1,z2,z3,z1104,z5,z13]),(0,[z1,z2,z4,z5,z819,z57]),(0,[z1,z2,z3,z4,z5,z403])],[(0,[z1,z2,z3,z1105,z4,z13]),(0,[z1,z216,z3,z4,z5,z206]),(0,[z1106,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z1,z2,z3,z10,z4,z94])],[(0,[z1,z2,z3,z1108,z5,z13]),(0,[z61,z1,z689,z3,z5,z13]),(0,[z1,z2,z3,z4,z5,z1109]),(0,[z1,z2,z3,z268,z5,z409])],[(0,[z63,z157,z3,z4,z5,z465]),(0,[z1,z2,z3,z4,z1110,z13]),(0,[z1111,z1,z3,z4,z5,z13]),(0,[z671,z1,z3,z4,z5,z17])],[(0,[z1,z2,z3,z225,z5,z206]),(0,[z1,z2,z3,z4,z5,z1112]),(0,[z1,z2,z3,z4,z5,z1113]),(0,[z1,z2,z3,z35,z5,z13]),(0,[z1114,z1,z2,z3,z5,z13]),(0,[z54,z70,z1,z2,z3,z13]),(0,[z1,z2,z3,z4,z1115,z13]),(0,[z44,z1,z2,z3,z10,z68])],[(0,[z73,z1,z242,z35,z5,z13]),(0,[z1,z2,z3,z4,z5,z1116]),(0,[z569,z1,z2,z4,z16,z13])],[(0,[z1,z1117,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1118])]],
   [[],[(0,[z1,z2,z3,z4,z5,z13]),(0,[z352,z2,z3,z52,z5,z13]),(0,[z1,z2,z3,z1119,z5,z13]),(0,[z1,z118,z3,z4,z5,z17]),(0,[z1,z2,z3,z4,z1120,z13])],[(0,[z1,z2,z3,z1121,z4,z5]),(0,[z104,z1,z2,z4,z1122,z13]),(0,[z1,z2,z1123,z4,z5,z13]),(0,[z0,z2,z3,z275,z114,z5]),(0,[z73,z1,z242,z4,z5,z13]),(0,[z1,z2,z3,z4,z13,z1124])],[(0,[z73,z1,z242,z231,z5,z13]),(0,[z1,z2,z377,z3,z22,z5]),(0,[z1,z3,z4,z55,z777,z13]),(0,[z1,z134,z598,z3,z4,z5]),(0,[z1,z2,z3,z268,z5,z13])],[(0,[z1,z2,z1125,z4,z5,z13]),(0,[z1,z2,z3,z90,z4,z132]),(0,[z1,z2,z3,z1126,z5,z13]),(0,[z1,z2,z3,z1127,z5,z13]),(0,[z1,z2,z3,z370,z4,z5]),(0,[z1,z2,z3,z300,z5,z80])],[(0,[z1,z2,z3,z4,z5,z404]),(0,[z105,z2,z78,z4,z5,z13]),(0,[z0,z113,z2,z3,z114,z5]),(0,[z1,z53,z3,z4,z71,z13]),(0,[z15,z1,z2,z4,z171,z13]),(0,[z1,z2,z3,z90,z491,z13]),(0,[z1,z2,z3,z58,z4,z68])],[(0,[z46,z11,z103,z4,z5,z13]),(0,[z1,z2,z3,z601,z4,z5]),(0,[z611,z1,z3,z4,z5,z17]),(0,[z1,z2,z142,z4,z744,z13])],[(0,[z1,z2,z3,z4,z1128,z5]),(0,[z44,z1,z2,z3,z363,z13]),(0,[z1,z2,z3,z1129,z4,z5])]],
   [[(0,[z104,z1,z242,z4,z5,z13]),(0,[z1,z201,z113,z2,z3,z4]),(0,[z9,z2,z3,z4,z129,z5]),(0,[z1,z2,z417,z4,z75,z13]),(0,[z1,z2,z3,z4,z13,z830])],[(0,[z1,z2,z3,z1130,z5,z13])],[(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z2,z1131,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1132])],[(0,[z1,z2,z3,z4,z5,z465]),(0,[z61,z1,z2,z188,z3,z13]),(0,[z1,z2,z3,z4,z1133,z13]),(0,[z1,z2,z3,z4,z349,z141]),(0,[z1,z2,z3,z210,z45,z67])],[(0,[z33,z1,z2,z3,z16,z13]),(0,[z2,z3,z4,z5,z96,z820]),(0,[z1,z2,z3,z4,z1134,z13]),(0,[z44,z1,z2,z64,z75,z13]),(0,[z1,z2,z286,z22,z171,z13]),(0,[z1,z2,z286,z733,z5,z13]),(0,[z15,z1,z2,z4,z16,z13]),(0,[z1,z2,z473,z4,z5,z57])],[(0,[z1,z2,z3,z4,z1122,z13]),(0,[z1,z201,z2,z3,z275,z4]),(0,[z44,z1,z2,z3,z4,z132]),(0,[z1,z2,z3,z5,z13,z1135]),(0,[z1,z2,z3,z4,z1136,z13]),(0,[z1,z2,z3,z4,z18,z13]),(0,[z44,z1,z2,z452,z91,z13]),(0,[z1,z2,z3,z4,z13,z94])],[(0,[z664,z1,z2,z64,z5,z13]),(0,[z1,z2,z3,z4,z405,z67]),(0,[z1,z2,z377,z3,z115,z4]),(0,[z1,z2,z3,z4,z5,z1137]),(0,[z1,z2,z144,z4,z75,z13]),(0,[z15,z1,z2,z268,z16,z13])],[(0,[z1,z2,z3,z1138,z4,z13]),(0,[z1,z2,z3,z4,z96,z94])]],
   [[(0,[z63,z157,z3,z4,z5,z339]),(0,[z1,z2,z3,z4,z371,z131]),(0,[z1,z128,z3,z725,z5,z13]),(0,[z1,z2,z3,z1139,z4,z5]),(0,[z1,z2,z3,z4,z18,z57])],[(0,[z1140,z1,z2,z3,z5,z13]),(0,[z1141,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z233,z94])],[(0,[z1,z2,z31,z4,z5,z13]),(0,[z554,z2,z3,z4,z5,z96]),(0,[z1,z2,z3,z350,z5,z151])],[(0,[z1,z2,z3,z4,z5,z1142]),(0,[z51,z2,z3,z685,z5,z13]),(0,[z439,z2,z3,z4,z5,z8])],[(0,[z1,z2,z1143,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1144]),(0,[z1,z2,z3,z4,z5,z1145]),(0,[z1,z2,z3,z97,z4,z75]),(0,[z1,z2,z3,z1146,z5,z13]),(0,[z1,z2,z3,z5,z13,z1147])],[(0,[z1,z2,z3,z1148,z5,z13]),(0,[z1,z2,z22,z733,z5,z13])],[(0,[z1,z2,z3,z1149,z5,z13]),(0,[z1,z2,z1150,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z1151]),(0,[z1,z128,z2,z188,z3,z13]),(0,[z1,z2,z733,z64,z5,z13]),(0,[z1,z2,z3,z4,z5,z1152])],[(0,[z1,z1153,z2,z3,z4,z5]),(0,[z43,z2,z3,z563,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z1154]),(0,[z1,z2,z3,z4,z5,z173]),(0,[z1,z2,z3,z1155,z5,z13])],[(0,[z1,z2,z3,z4,z13,z1156]),(0,[z2,z3,z4,z774,z5,z13]),(0,[z1,z2,z3,z4,z5,z1157])],[(0,[z1,z2,z3,z10,z313,z5]),(0,[z1,z2,z3,z1158,z5,z13]),(0,[z44,z1,z2,z3,z5,z260])],[(0,[z1,z2,z3,z4,z1159,z13]),(0,[z1,z2,z3,z4,z1160,z5]),(0,[z1,z1161,z3,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z1162])],[(0,[z1,z203,z3,z4,z5,z131]),(0,[z250,z2,z3,z4,z28,z13]),(0,[z1,z2,z3,z4,z1163,z5]),(0,[z110,z1,z2,z3,z211,z5]),(0,[z1,z2,z3,z350,z16,z13]),(1,[z1,z2,z4,z5,z819])],[(0,[z1,z2,z3,z601,z318,z5]),(0,[z359,z2,z3,z4,z445,z13]),(0,[z44,z1,z2,z3,z45,z80])],[(0,[z1,z2,z3,z4,z5,z339]),(0,[z359,z2,z3,z4,z277,z13]),(0,[z61,z1,z3,z186,z5,z227]),(0,[z1,z2,z3,z4,z777,z13]),(0,[z1,z2,z3,z1164,z5,z13]),(0,[z110,z1,z2,z3,z4,z94])]],
   [[(0,[z1,z2,z3,z4,z1165,z5]),(0,[z1166,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z748,z91,z13])],[(0,[z1,z216,z3,z4,z371,z13]),(0,[z1,z2,z3,z4,z5,z1167]),(0,[z1,z3,z23,z725,z5,z13])],[(0,[z1,z2,z3,z4,z1168,z13]),(0,[z1,z2,z3,z1169,z5,z13]),(0,[z1,z2,z423,z4,z75,z13]),(0,[z1,z2,z3,z4,z67,z830])],[(0,[z1,z2,z3,z4,z5,z1170]),(0,[z27,z2,z3,z4,z482,z13]),(0,[z1,z2,z3,z4,z5,z87]),(0,[z524,z1,z2,z64,z5,z13]),(0,[z1,z2,z3,z210,z13,z68])],[(0,[z1,z2,z3,z1171,z4,z13]),(0,[z1,z2,z3,z225,z371,z13]),(0,[z33,z1,z2,z3,z32,z5]),(0,[z1,z2,z3,z64,z5,z161])],[(0,[z1,z2,z1172,z3,z4,z13]),(0,[z1,z203,z3,z4,z226,z13]),(0,[z1,z1173,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z1174,z13]),(0,[z1,z2,z188,z3,z370,z4]),(0,[z1,z2,z3,z4,z1175,z5]),(0,[z1,z2,z3,z4,z5,z1176]),(0,[z1,z2,z3,z4,z5,z816])],[(0,[z1,z2,z3,z4,z1177,z13]),(0,[z121,z1,z2,z733,z5,z13]),(0,[z1,z2,z3,z64,z101,z13])],[(0,[z1,z2,z3,z1178,z5,z13]),(0,[z1,z2,z3,z4,z5,z1179]),(1,[z2,z3,z741,z5,z13]),(0,[z0,z1,z201,z2,z3,z13]),(0,[z1,z53,z3,z4,z71,z87])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 536).take 547) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1083).take 47) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1130)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [536, 547, 47] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 136).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 136).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [136, 120] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_39019

theorem PEqualNP.Outside.L_meta_39019 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276812992 * 2 ^ 32 + 4243127424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276812992 * 2 ^ 32 + 4243127424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39019.solve