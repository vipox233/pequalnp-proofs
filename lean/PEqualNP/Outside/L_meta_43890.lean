import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43890

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

theorem tierB {S : ℕ × List W → Bool} {J d K : ℕ} (hK : J + d = K) {L : List (ℕ × List W)} {sizes : List ℕ}
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false)
    (hw : windowsG (chunkB S d) L 0 sizes = true) : FalseAt K L := by
  subst hK
  have hP := windowsG_sound (P := fun c => optB S d c.1 c.2 = false)
    (fun X hX c hc => by have := List.all_eq_true.mp hX c hc; simpa using this) sizes 0 hw
  intro c hc
  exact optB_sound S J hS d c.1 c.2 (hP c (by simpa using hc))

theorem memS {g nb J : ℕ} {bk : List (List (List (ℕ × List W)))} (h : FalseAt J bk.flatten.flatten) :
    ∀ c, (!inB2 g nb bk c) = false → optimized J c.1 c.2 = false := by
  intro c hc
  have hin : inB2 g nb bk c = true := by simpa using hc
  exact h c (inB2_mem hin)

theorem finalF {J : ℕ} {bk : List (List (List (ℕ × List W)))} {sizes : List ℕ}
    (h : windowsF J bk.flatten 0 sizes = true) : FalseAt J bk.flatten.flatten := by
  have := falseAt_of_windowsF sizes 0 h
  simpa using this

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4276791424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def rows : List W :=
  [(mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff04e463f018ffff),
   (mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1b5b9cc8e7323f),
   (mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe39c1f0f07c3c7),
   (mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc1fe00ff803f8),
   (mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffe0000ffffc00),
   (mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fffffff0000000)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [13, 14]⟩], 15⟩

def z0 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1b5b9cc8e7323f

def z1 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fffffff0000000

def z2 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff04e463f018ffff

def z3 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc1fe00ff803f8

def z4 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffe0000ffffc00

def z5 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0xfffffffffffff800 0x00fffffffffffc00

def z6 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe39c1f0f07c3c7

def z7 : W := mkw 0x8918a33042238000 0x002c0000036b5400 0xfffffffffffff800 0x00fc00000ffffc00

def z8 : W := mkw 0x000d441288509220 0x22124308c0c2302c 0x001ffc0000780000 0xf0184380c0e03038

def z9 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x00001ffff0000000

def z10 : W := mkw 0x008c5418a8508288 0xaa12531848c61209 0x0000fc01f8000000 0x001b1b9c08e70000

def z11 : W := mkw 0x3002004400886141 0x1100004220108992 0xf00003c00787f81f 0x0004a4633018cdc0

def z12 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x00001b9c00000000

def z13 : W := mkw 0x5280100420002458 0x88801c020c008342 0xffe0003e078007ff 0x0fe09c030f00c3c7

def z14 : W := mkw 0x8d10a32146270000 0x006da00003294400 0xffe003ffff87f800 0x00e7a0000f1fcc00

def z15 : W := mkw 0x0001000200001020 0x0000000080002024 0x001f003e007807e0 0xff004000c000323f

def z16 : W := mkw 0x308f545ea8d8f3e9 0xbb12535ae8d6bbbf 0xf01fffffffffffff 0xff1ffffff8ffffff

def z17 : W := mkw 0x0a00820000000010 0x00ac0dad50000000 0x0000000000000000 0x00fc1ffff0000000

def z18 : W := mkw 0x2002000000004100 0x0000004000100090 0xf01f03c0000007ff 0xf0040460001803f8

def z19 : W := mkw 0x7ad79ac6208a777d 0xd9ac1ee2adb8abfe 0xfffffffe07ffffff 0xfffcffe3fff8ffff

def z20 : W := mkw 0xd2a0102c310124da 0x8c801c120e05c343 0xffe0003fff8007ff 0x0fe01c000f07c3c7

def z21 : W := mkw 0x4ad49a802002061c 0xc8ac1ea00da80248 0x0fe0fc0000000000 0x00f81b800fe00000

def z22 : W := mkw 0x8d10a32146270000 0x006da00003294400 0xffe003c00787f800 0x00e4a0000718cc00

def z23 : W := mkw 0x8d9df73bee7792a8 0xaa7ff318cbef762d 0xffffffffffffffe0 0xfffffb9ccffffe3f

def z24 : W := mkw 0x0080100820000088 0x8800101008040201 0x0000003ff80007e0 0x0f03181c08070207

def z25 : W := mkw 0xd620002515012452 0x04c18c070601c142 0xffe000000780001f 0x00e084030700c1c0

def z26 : W := mkw 0x0810820000020000 0x002c000001280000 0xfffffffe07fff800 0x00fce0000ff8fc00

def z27 : W := mkw 0x0009441a885090a0 0x22124118c0463025 0x001ffc3ff8780000 0x0f1b401cc8e73007

def z28 : W := mkw 0x0c00c20184440000 0x007fe00000000000 0x0000000000000000 0x00ffe463f0000000

def z29 : W := mkw 0x52a0100c310024da 0x8c801c170c048343 0x00000000000007ff 0x0f001c1f000003c7

def z30 : W := mkw 0x3a03824600887171 0x11ac0ce2a010a9b6 0xf01f03fe07ffffff 0xfffcffe3f018ffff

def z31 : W := mkw 0x9d19e377c6efb061 0x117fe002a36bfd26 0xfffffffffffff800 0x0fffe003fffffc07

def z32 : W := mkw 0x0400400184440000 0x0053e10d50000000 0x0000000000000000 0x0003e01ff0000000

def z33 : W := mkw 0x8d18e331c6678000 0x007fe10d536b5400 0xfffffffffffff800 0x00ffe01ffffffc00

def z34 : W := mkw 0x1001004600883061 0x11000002a000a926 0xf01f03fe07fff800 0x0f04e003f018fc07

def z35 : W := mkw 0x7ad79ac6208a777d 0xd9ac1ee2adb8abfe 0xfffffffe07ffffff 0xfffc1fe00ff8ffff

def z36 : W := mkw 0x0000400080400000 0x0012410840000000 0x0000000000000000 0x001b5b9cc0000000

def z37 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xfffffffe07ffffff 0xf0fcffe00ff8fff8

def z38 : W := mkw 0x6adfde9aa852d7bc 0xeabe5ff8cdfe32fd 0xfffffffff87807ff 0xffff5ffccfff33ff

def z39 : W := mkw 0x8d9df73bee7792a8 0xaa7ff2108bef762d 0xffffffffffffffe0 0xffffe0000ffffe3f

def z40 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0004e463f0000000

def z41 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1ffffff8e7323f

def z42 : W := mkw 0x028d541aa85092b8 0xaa925fbdd8c6322d 0x001ffc3ff87807e0 0xff1b5ffff8e7323f

def z43 : W := mkw 0x0918e310c2668000 0x003e6000016a1400 0x001fffc0007ff800 0x001c600000f83c00

def z44 : W := mkw 0x8118213042238000 0x00000000036b5400 0x0fe0fc01f8000000 0x000000000fe70000

def z45 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0x0fe00001f80007ff 0x0fe31c1f0f0703c7

def z46 : W := mkw 0x3e03c24784cc7171 0x11ffedeff010a9b6 0xf01f03fe07ffffff 0xfffffffff018ffff

def z47 : W := mkw 0x0004000000000200 0x0000020000800008 0x001ffc0000000000 0xf018038000e00038

def z48 : W := mkw 0x0400000104000000 0x0041800000000000 0x0000000000000000 0x00e3800000000000

def z49 : W := mkw 0x0d18e311c6668000 0x007fe000016a1400 0x001fffc0007ff800 0x00ffe00000f83c00

def z50 : W := mkw 0xd6ad543fbd51b6fa 0xaed3df1fcec7f36f 0xfffffc3ffff807ff 0xfffbdf9fcfe7f3ff

def z51 : W := mkw 0x0e8cd619ac548298 0xaaffffbd58c61209 0x0000fc01f8000000 0x00fb1b9c08e70000

def z52 : W := mkw 0x2003004200885121 0x11000040a01028b4 0x001f03c0007ff800 0xf004e463f0183c38

def z53 : W := mkw 0x9020002c110120c2 0x040000120205c103 0x0000003fff800000 0x0f0000000007c007

def z54 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffff03ffffffffff 0x0fe7fc1f0f1fffc7

def z55 : W := mkw 0x0810820000020000 0x002c000001280000 0xffffffc000000000 0x00fc00000ff80000

def z56 : W := mkw 0x85086131c6658000 0x0053e00002435400 0x0000003ffffff800 0x0003e0000007fc00

def z57 : W := mkw 0x0c00c20184440000 0x007fe10d50000000 0x0000000000000000 0x00ffe01ff0000000

def z58 : W := mkw 0xf0f618ac310367ce 0xcc0012520fbdc3db 0xffffffffff8007ff 0xff0000000fffc3ff

def z59 : W := mkw 0x28568a8000024304 0x402c02e001b80098 0x001fffc000000000 0xf01c03e000f80038

def z60 : W := mkw 0x62c618802000471c 0xc8801ee00c9002d8 0x00000000000007ff 0xf0001fe0000003f8

def z61 : W := mkw 0x6ed6da81a446471c 0xc8ffffed5db802d8 0xffffffc0000007ff 0xf0fffffffff803f8

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0xf01f03fe07fff800 0x0004e0000018fc00

def z63 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0x00000000000007ff 0xff000463f00003ff

def z64 : W := mkw 0x0000000000000000 0x0000010d50000000 0x0000000000000000 0x0000001ff0000000

def z65 : W := mkw 0x6ad29a802002451c 0xc8ac1ce00d3802d0 0xffe003c0000007ff 0x00e41c600f1803c0

def z66 : W := mkw 0x8118213042238000 0x00000000036b5400 0xfffffffffffff800 0x000000000ffffc00

def z67 : W := mkw 0x85086131c6658000 0x0053e00002435400 0xf01f03fffffff800 0x0007e000001ffc00

def z68 : W := mkw 0x0918e310c2668000 0x003e61a8516a1400 0x001fffc0007ff800 0x001c63e0f0f83c00

def z69 : W := mkw 0xdfb8f33df767a4da 0x8cfffc170f6fd743 0xffffffffffffffff 0x0ffffc1f0fffffc7

def z70 : W := mkw 0xf6a3106f358975fb 0x9dc19c57ae15ebf7 0xffff03ffffffffff 0xffe7fc7fff1fffff

def z71 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00ff1ffc00000000

def z72 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x0000fc01f80007e0 0xff1b1b9cc8e7023f

def z73 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff184380c8e7323f

def z74 : W := mkw 0x080dc61288549220 0x223e63a8d0c2302c 0x001ffc0000780000 0xf01c63e0f0e03038

def z75 : W := mkw 0xc6a010293501049a 0x8cc19c150e054241 0x0fe00001f8000000 0x00e3181c0f070000

def z76 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x0004fffff0000000

def z77 : W := mkw 0x50a0100c310024ca 0x8c0010120c048343 0x00000000000007ff 0x0f000000000003c7

def z78 : W := mkw 0x0f18e311c6668010 0x00ffedad516a1400 0x001fffc0007ff800 0x00fffffff0f83c00

def z79 : W := mkw 0x4280100020000418 0x88801c000c000240 0xffe00000000007ff 0x00e01c000f0003c0

def z80 : W := mkw 0xfef69aad350367de 0xcced9ef70fbdc3db 0xffffffffff8007ff 0xffff9fff0fffc3ff

def z81 : W := mkw 0x72a3104e318875fb 0x9d801c57ac14abf7 0x00000000000007ff 0xff001c7ff00003ff

def z82 : W := mkw 0xb403006704897161 0x11418042a211e9b6 0xffff03ffffffffff 0xffe7e463ff1fffff

def z83 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff0000000018ffff

def z84 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00fb00000ffffc00

def z85 : W := mkw 0x0e00820104040010 0x00edaca510000000 0x0000000000000000 0x00e4a46330000000

def z86 : W := mkw 0xad5eebb1c667c304 0x407fe2e003fb5498 0xfffffffffffff800 0xf0ffe3e00ffffc38

def z87 : W := mkw 0x0008401080408000 0x0012400000421000 0x001ffc3ff8780000 0x001b400008e73000

def z88 : W := mkw 0x0085140a281012a8 0xaa001318c884222d 0x00000000000007e0 0xff001b9cc000023f

def z89 : W := mkw 0x0a00820000000010 0x00ac0ca000000000 0x0000000000000000 0x00fc1fe000000000

def z90 : W := mkw 0x1000004400882041 0x1100000220008902 0x000000000787f800 0x0000a0033000cc00

def z91 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffe463fffffc00

def z92 : W := mkw 0xffbbf37ff7eff5fb 0x9dfffc57af7ffff7 0xffffffffffffffff 0xfffffc7fffffffff

def z93 : W := mkw 0x1000000400002040 0x0000000200008102 0xf00000000780001f 0x000084030000c1c0

def z94 : W := mkw 0x52a0100c310024da 0x8c801c170c048343 0xffe00000000007ff 0x0fe01c1f0f0003c7

def z95 : W := mkw 0xde20c22595452452 0x04ffedaf5601c142 0xffe000000780001f 0x00fffffff700c1c0

def z96 : W := mkw 0x0085140a281012a8 0xaa0012108884222d 0x00000000000007e0 0xff0000000000023f

def z97 : W := mkw 0x2002000000004100 0x0000004000100090 0xf01f03c0000007ff 0xf004e463f01803f8

def z98 : W := mkw 0x2002000000004100 0x0000004000100090 0xf01f03fe07ffffff 0xf004e4600018fff8

def z99 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf000003e078007ff 0xff008463f000c3ff

def z100 : W := mkw 0x0000000000000000 0x000001a850000000 0x0000000000000000 0x000003e0f0000000

def z101 : W := mkw 0x0009441a885090a0 0x22124118c0463025 0x0000003ff8780000 0x0f03401cc0073007

def z102 : W := mkw 0x6a528a8000024514 0x40ac0ce0053800d0 0xffe003c00000001f 0x00e40460071801c0

def z103 : W := mkw 0x2856ca8080464304 0x403e63e851b80098 0x001fffc000000000 0xf01c63e0f0f80038

def z104 : W := mkw 0x0008401080408000 0x0012400000421000 0x0000fc01f8000000 0x001b000008e70000

def z105 : W := mkw 0x0c00c20184440000 0x007fe00000000000 0xf01f03fe07fff800 0x00ffe0000018fc00

def z106 : W := mkw 0x62c618802000471c 0xc8801ee00c9002d8 0x001ffc00000007ff 0xf0181fe008e003f8

def z107 : W := mkw 0x7a538ac6008a7575 0x51ac0ce2a538a9f6 0xffff03fe07ffffff 0xffe4e463f718ffff

def z108 : W := mkw 0xcea0d229b545049a 0x8cfffdbd5e054241 0x0fe00001f8000000 0x00fb1b9c0f070000

def z109 : W := mkw 0x008d141a281092a8 0xaa00121088c6322d 0x001ffc3ff87807e0 0xff00000008e7323f

def z110 : W := mkw 0x6a528a8000024514 0x40ac0ce0053800d0 0xffffffc00000001f 0x00fc04600ff801c0

def z111 : W := mkw 0x8d10a32146270000 0x006da00003294400 0x0fe0000000000000 0x00e0000007000000

def z112 : W := mkw 0x9420002d150120c2 0x044180170205c103 0x0000003fff800000 0x0f03801f0007c007

def z113 : W := mkw 0xbf1be377c6eff171 0x11ffedeff37bfdb6 0xffffffffffffffff 0xffffffffffffffff

def z114 : W := mkw 0x0e8dd61bac5492b8 0xaaffffbdd8c6322d 0x001ffc3ff87807e0 0xfffffffff8e7323f

def z115 : W := mkw 0x0600000104000010 0x00c18c0500000000 0x0000000000000000 0x00e3181c00000000

def z116 : W := mkw 0x8400002104010000 0x0041800002014000 0xffe0003fff800000 0x00e380000f07c000

def z117 : W := mkw 0x60d618802002470c 0xc80012400db802d8 0xffffffc0000007ff 0xf00000000ff803f8

def z118 : W := mkw 0x0084100020000208 0x8800120008800208 0x001ffc00000007e0 0xf0181b8008e00238

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000003e07fff800 0x0000e0000000fc00

def z120 : W := mkw 0x8480102924010088 0x884190100a054201 0xffe0003fff8007e0 0x0fe3981c0f07c207

def z121 : W := mkw 0xefd6bba16627471c 0xc8edbee00fb946d8 0xffffffc00787ffff 0xf0fcbfe00ff8cff8

def z122 : W := mkw 0x0001000200001020 0x0000000080002024 0xf01f03fe07ffffe0 0xff04e000c018fe3f

def z123 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc01f8780000 0xf01b5b9cc8e73038

def z124 : W := mkw 0x0800c20080440000 0x003e61a850000000 0x0000000000000000 0x001c63e0f0000000

def z125 : W := mkw 0x8518213146238000 0x00418000036b5400 0xfffffffffffff800 0x00e380000ffffc00

def z126 : W := mkw 0x28578ac2008a5325 0x512c02e0a1b828bc 0x001fffc0007ff800 0xf01c63e0f0f83c38

def z127 : W := mkw 0x7ad69a842002675c 0xc8ac1ee20db883da 0xfffffffe078007ff 0xfffc9fe30ff8c3ff

def z128 : W := mkw 0x008c5418a8508288 0xaa12531848c61209 0x001ffc01f80007e0 0xf01b1b9c08e70238

def z129 : W := mkw 0xcea0d229b545049a 0x8cfffdbd5e054241 0x0fe00001f8000000 0x00ffffffff070000

def z130 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0xf01f03fe07fff800 0x00fffffff018fc00

def z131 : W := mkw 0x1001004600883061 0x11000002a000a926 0x0000003e07fff800 0x0f00e003f000fc07

def z132 : W := mkw 0xd4a0102d350124ca 0x8c4190120e05c343 0xffe0003fff8007ff 0x0fe380000f07c3c7

def z133 : W := mkw 0xeed69aa12403471c 0xc8ed9ee00fb942d8 0xffffffffff8007ff 0xf0ff9fe00fffc3f8

def z134 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0x0fe0fc00000007ff 0xf0f81fe00fe003f8

def z135 : W := mkw 0x0a00c20080440010 0x00be6dad50000000 0x0000000000000000 0x001c7ffff0000000

def z136 : W := mkw 0x2e56ca8184464314 0x40ffefed51b80098 0x001fffc000000000 0xf0fffffff0f80038

def z137 : W := mkw 0x62c618802000471c 0xc8801fed5c9002d8 0x00000000000007ff 0xf0001ffff00003f8

def z138 : W := mkw 0x300f445688d8f361 0x3312434ae0d2b9be 0xf01ffffe07ffffff 0xff1ce7e3f0f8ffff

def z139 : W := mkw 0x819d353a6a3392a8 0xaa0012108bef762d 0xffffffffffffffe0 0xff0000000ffffe3f

def z140 : W := mkw 0x308f545ea8d8f3e9 0xbb12535ae8d6bbbf 0x001ffc3ff87807ff 0xff1b5ffff8e733ff

def z141 : W := mkw 0x848d543bac5192a8 0xaa53d318cac7722d 0xfffffc3ffff807e0 0xfffbdb9ccfe7f23f

def z142 : W := mkw 0xd620002d150124d2 0x04c18c170605c143 0xffe0003fff80001f 0x0fe3841f0707c1c7

def z143 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc00007807e0 0xff185b9cc0e0323f

def z144 : W := mkw 0x72c718c62088777d 0xd9801ee2ac90abfe 0xf01f03fe07ffffff 0xff04ffe3f018ffff

def z145 : W := mkw 0x2003004200885121 0x11000040a01028b4 0x0000000000000000 0xf0000060f0000038

def z146 : W := mkw 0x0009441a885090a0 0x22124118c0463025 0x001f003ff87807e0 0xff03401cc007323f

def z147 : W := mkw 0xd6a0102d350124da 0x8cc19dbf5e05c343 0xffe0003fff8007ff 0x0fe39fffff07c3c7

def z148 : W := mkw 0x0c00c20184440000 0x007fe00000000000 0x0000000000000000 0x00ffe00000000000

def z149 : W := mkw 0x0c00c20184440000 0x007fe10840000000 0x0000000000000000 0x00fffb9cc0000000

def z150 : W := mkw 0x0008401080408000 0x0012400000421000 0x001ffc0000780000 0x0018400000e03000

def z151 : W := mkw 0x2056088000024304 0x4000024001b80098 0x001fffc000000000 0xf000000000f80038

def z152 : W := mkw 0x008d141a281092a8 0xaa001318c8c6322d 0x001ffc3ff87807e0 0xff001b9cc8e7323f

def z153 : W := mkw 0x62c618802000471c 0xc8801ee00c9002d8 0xffe00000000007ff 0xf0e01fe00f0003f8

def z154 : W := mkw 0x0600000104000010 0x00c18c0500000000 0x0000000000000000 0x00e39c1f00000000

def z155 : W := mkw 0xdea0d22db54524da 0x8cfffdbf5e05c343 0xffe0003fff8007ff 0x0fffffffff07c3c7

def z156 : W := mkw 0xbd1be377c6eff161 0x117fe042a37bfdb6 0xffffffffffffffff 0xffffe463ffffffff

def z157 : W := mkw 0x7a528ac4008a6555 0x51ac0ce2253889d2 0xffe003c00787f81f 0x00e4a4633718cdc0

def z158 : W := mkw 0x0008001000008000 0x0000000000421000 0x001ffc3ff8780000 0x0000000008e73000

def z159 : W := mkw 0xd0a0102c310124ca 0x8c0010120e05c343 0xffe0003fff8007ff 0x0f0000000f07c3c7

def z160 : W := mkw 0x2046088000004304 0x400002e000900098 0x0000000000000000 0xf00003e000000038

def z161 : W := mkw 0xd6a5142f3d1136fa 0xaec19f1fce85e36f 0xffe0003fff8007ff 0xffe39f9fcf07c3ff

def z162 : W := mkw 0x9421006f158930e3 0x15418017a205e927 0x0000003ffffff800 0x0f03e01ff007fc07

def z163 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00046060f0000000

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0004a46330000000

def z165 : W := mkw 0x85086131c6658000 0x0053e00002435400 0x001ffc3ffffff800 0x001be00008e7fc00

def z166 : W := mkw 0xbd1ae375c6efe141 0x117fe042237bdd92 0xfffffffffffff81f 0x00ffe4633ffffdc0

def z167 : W := mkw 0xefdefbb1e667c71c 0xc8fffee00ffb56d8 0xffffffffffffffff 0xf0ffffe00ffffff8

def z168 : W := mkw 0x1001004600883061 0x11000002a000a926 0x0000003e07fff800 0x0f04e463f000fc07

def z169 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0x0fe0fc01f8000000 0x00fb00000fe70000

def z170 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0x0fe0fc01f8000000 0x00ffe0000fe70000

def z171 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff00e003f018ffff

def z172 : W := mkw 0x60df1c9a2812d7ac 0xea0012508dfe32fd 0xfffffffff87807ff 0xff0000000fff33ff

def z173 : W := mkw 0x0a00820000000010 0x00ac0ca000000000 0x0000000000000000 0x00e4046000000000

def z174 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fb1b9c00000000

def z175 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0xf01fffffffffffe0 0xff1ffb9cc8fffe3f

def z176 : W := mkw 0x0200000000000010 0x00800c0500000000 0x0000000000000000 0x00001c1f00000000

def z177 : W := mkw 0xf6af547fbdd9f7fb 0xbfd3df5feed7fbff 0xffffffffffffffff 0xffffffffffffffff

def z178 : W := mkw 0x8f08e331c6658010 0x00ffedad52435400 0x0000003ffffff800 0x00fffffff007fc00

def z179 : W := mkw 0x048d541bac5492a8 0xaa53f31dd8c6322d 0x001ffc3ff87807e0 0xff1bfb9ff8e7323f

def z180 : W := mkw 0x0910a30042260000 0x002c200001280400 0x000003c00007f800 0x0004200000180c00

def z181 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0x0fe0fc01f8000000 0x00fb1b9c0fe70000

def z182 : W := mkw 0x0001400280401020 0x00124108c0002024 0x001f003e007807e0 0xff1b5b9cc000323f

def z183 : W := mkw 0x0010000000020000 0x0000000001280000 0xffffffc000000000 0x000000000ff80000

def z184 : W := mkw 0x0084140828100288 0xaa00131848840209 0x0000000000000000 0x00001b9c00000000

def z185 : W := mkw 0x1000000400002040 0x0000000200008102 0xf000003e078007ff 0x0f0084030000c3c7

def z186 : W := mkw 0xf0a3106e318975eb 0x9d001052ae15ebf7 0xffff03ffffffffff 0xff0000000f1fffff

def z187 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe7fc7fff07c3c7

def z188 : W := mkw 0x85086131c6658000 0x0053e10d52435400 0x0000003ffffff800 0x0003e01ff007fc00

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z190 : W := mkw 0x40d418802002060c 0xc80012000da80248 0x0fe0fc0000000000 0x000000000fe00000

def z191 : W := mkw 0xdfb8f33df767a4da 0x8cfffc170f6fd743 0xffe0fc3fff8007ff 0x0ffb9c1f0fe7c3c7

def z192 : W := mkw 0x8f10a32146270010 0x00edaca513294400 0xffe003c00787f800 0x00e4a4633718cc00

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0xf01f03c000000000 0x0004000000180000

def z194 : W := mkw 0x200f445288d8d321 0x33124348e0d238bc 0x001fffc0007ff800 0xf01c63e0f0f83c38

def z195 : W := mkw 0x285fce928852d324 0x623e43e8c1fa30bc 0x001fffc000780000 0xf01c43e0c0f83038

def z196 : W := mkw 0x0600400184440010 0x00d3ed0d50000000 0x0000000000000000 0x00e3fc1ff0000000

def z197 : W := mkw 0x000d441a885092a0 0x22124318c0c6302d 0x001ffc3ff8780000 0xff1b439cc0e7303f

def z198 : W := mkw 0x1000000400002040 0x0000000200008102 0xf000003e078007ff 0x0f04e463f000c3c7

def z199 : W := mkw 0x1009445e88d8b0e1 0x3312411ae046b927 0x0000003ffffff800 0x0f03e01ff007fc07

def z200 : W := mkw 0x4680100124000418 0x88c19c050c000240 0xffe00000000007ff 0x00e39c1f0f0003c0

def z201 : W := mkw 0x308f145e2898f3e9 0xbb001252a8d6bbbf 0xf01fffffffffffff 0xff00000008ffffff

def z202 : W := mkw 0xfaf69aac310367de 0xccac1ef20fbdc3db 0xffffffffff8007ff 0xfffc1fe00fffc3ff

def z203 : W := mkw 0xd6a1102f350134fa 0x8cc19c178e05e367 0xffff003ffff807ff 0xffe3dc1fcf07f3ff

def z204 : W := mkw 0xf6e618ad350167de 0xccc19ef70e95c3db 0xffe0003fff8007ff 0xffe39fff0f07c3ff

def z205 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fb9f9f00000000

def z206 : W := mkw 0xc6a010293501049a 0x8cc19c150e054241 0x0fe00001f8000000 0x00e39c1f0f070000

def z207 : W := mkw 0xf622006515896553 0x15c18c472611c9d2 0xffe003c00787f81f 0x00e4a4633718cdc0

def z208 : W := mkw 0xcfb8f339f767849a 0x8cfffc150f6f5641 0xfffffffffffff800 0x00fff81c0ffffc00

def z209 : W := mkw 0x6ac69a802000471c 0xc8ac1ee00c9002d8 0x00000000000007ff 0xf0fc1fe0000003f8

def z210 : W := mkw 0x0118211042228000 0x00000000016a1400 0x001fffc0007ff800 0x0000000000f83c00

def z211 : W := mkw 0x9420002d150120c2 0x044180170205c103 0xffe0003fff800000 0x0fe3801f0f07c007

def z212 : W := mkw 0xcf98f331e6678418 0x88fffc000f6b5640 0xffffffffffffffff 0x00fffc000fffffc0

def z213 : W := mkw 0x391be356c2eef161 0x113e6042a17abdb6 0xf01ffffe07ffffff 0xff1ce463f0f8ffff

def z214 : W := mkw 0x4adcde98a852869c 0xeabe5fb84dee1249 0x0fe0fc01f8000000 0x00fb1b9c0fe70000

def z215 : W := mkw 0x6ed6da81a446471c 0xc8ffffed5db802d8 0xffffffc0000007ff 0xf0ff1ffc0ff803f8

def z216 : W := mkw 0x2003004200885121 0x11000040a01028b4 0x001f03c0007ff800 0xf0046060f0183c38

def z217 : W := mkw 0x0080100820000088 0x8800101008040201 0x0000003ff80007e0 0x0f00000008070207

def z218 : W := mkw 0x9400002504012040 0x004180020201c102 0xffe0003fff8007ff 0x0fe384030f07c3c7

def z219 : W := mkw 0x0a00c20080440010 0x00be6da850000000 0x0000000000000000 0x00fc7fe0f0000000

def z220 : W := mkw 0x3002004400886141 0x1100004220108992 0xf00003c00787f81f 0x000000000018cdc0

def z221 : W := mkw 0x4e80d201a4440418 0x88fffdad5c000240 0xffe00000000007ff 0x00ffffffff0003c0

def z222 : W := mkw 0x52a0100c310024da 0x8c801c170c048343 0xf000003e078007ff 0x0f009c1f0000c3c7

def z223 : W := mkw 0x6a528a8000024514 0x40ac0ce0053800d0 0xffff03c0000007ff 0xf0e40460071803f8

def z224 : W := mkw 0xd6a0502db54524da 0x8cd3fd1f5e05c343 0xffe0003fff8007ff 0x0fe3fc1fff07c3c7

def z225 : W := mkw 0xfef6daadb54767de 0xccffffff5fbdc3db 0xffffffffff8007ff 0xffffffffffffc3ff

def z226 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff046060f018ffff

def z227 : W := mkw 0x0000400080400000 0x0012410840000000 0x0000000000000000 0x0003401cc0000000

def z228 : W := mkw 0xdea0922d350524da 0x8cedbcb71e05c343 0xffe0003fff8007ff 0x0fe7bc7f3f07c3c7

def z229 : W := mkw 0x300b445e88d8f1e1 0x3312415ae056b9b7 0xf01f03ffffffffff 0xff07e47ff01fffff

def z230 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0x0fe0003fff800000 0x0fe3981f0f07c007

def z231 : W := mkw 0x0800820000000000 0x002c000000000000 0x0000000000000000 0x00fc000000000000

def z232 : W := mkw 0x4ed4da81a446061c 0xc8ffffad5da80248 0x0fe0fc0000000000 0x00fb1b9c0fe00000

def z233 : W := mkw 0x0400400184440000 0x0053e00000000000 0x0000000000000000 0x0003e00000000000

def z234 : W := mkw 0x000d441288509220 0x22124308c0c2302c 0x001ffc3e007807e0 0xff184380c0e0323f

def z235 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff04e0000018ffff

def z236 : W := mkw 0x008c5010a0408208 0x8812520008c21208 0x001ffc3ff87807e0 0xf01b5b8008e73238

def z237 : W := mkw 0x01086110c2648000 0x0012600000421400 0x00000000007ff800 0x0000600000003c00

def z238 : W := mkw 0x0008401080408000 0x0012400000421000 0xf01ffffffffff800 0x001fe00008fffc00

def z239 : W := mkw 0x0600000104000010 0x00c18c0500000000 0x0000000000000000 0x00e7fc7ff0000000

def z240 : W := mkw 0xfef29aad350365de 0xcced9cf70f3dc3d3 0xffe003ffff8007ff 0x0fe79c7f0f1fc3c7

def z241 : W := mkw 0x8e00c22184450010 0x00ffedad52014000 0xffe0003fff800000 0x00ffffffff07c000

def z242 : W := mkw 0xcfb8f339f767849a 0x8cfffc150f6f5641 0x0fe0fc01f8000000 0x00fb181c0fe70000

def z243 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03c0000007ff 0xff040463f01803ff

def z244 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff0404600018ffff

def z245 : W := mkw 0x300b405680c8f161 0x11124042a052b9b6 0xf01fffffffffffff 0xff1fe463f8ffffff

def z246 : W := mkw 0x0e00820104000010 0x00ed8ca500000000 0x0000000000000000 0x00ff9fff00000000

def z247 : W := mkw 0x3403404784cc7161 0x1153e14ff010a9b6 0xf01f03fe07ffffff 0xff07e47ff018ffff

def z248 : W := mkw 0x0080100820000088 0x8800101008040201 0x00000001f8000000 0x0003181c08070000

def z249 : W := mkw 0x8600002104010010 0x00c18c0502014000 0xffe0003fff800000 0x00e39c1f0f07c000

def z250 : W := mkw 0x0680100924000098 0x88c19c1508040201 0x0000003ff80007e0 0x0fe39c1f08070207

def z251 : W := mkw 0x6ed69a812402471c 0xc8ed9ee50db802d8 0xffffffc0000007ff 0xf0ff9fff0ff803f8

def z252 : W := mkw 0x4ad49a802002061c 0xc8ac1ea00da80248 0x0ffffc00000007e0 0xf0f81b800fe00238

def z253 : W := mkw 0x72a3104e318875fb 0x9d801c57ac14abf7 0xf01f03fe07ffffff 0xff04fc7ff018ffff

def z254 : W := mkw 0x008d5412a8509228 0xaa125308c8c2322c 0x001ffc00007807e0 0xf0185b80c8e03238

def z255 : W := mkw 0x7283104620887579 0x99801c42ac10abf6 0xffff03fe07ffffff 0xffe4fc63ff18ffff

def z256 : W := mkw 0x8d18e331c6678000 0x007fe1a8536b5400 0xfffffffffffff800 0x00ffe3e0fffffc00

def z257 : W := mkw 0x0a00820000000010 0x00ac0ca000000000 0x0000000000000000 0x00f81b8000000000

def z258 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fce7e3f0000000

def z259 : W := mkw 0x60df5c9aa852d7ac 0xea125358cdfe32fd 0xfffffffff87807ff 0xff1b5b9ccfff33ff

def z260 : W := mkw 0xd6ac543dbd51a6da 0xaed3df1f4ec7d34b 0xffe0fc3fff8007ff 0x0ffb9f9f0fe7c3c7

def z261 : W := mkw 0x0e00820104040010 0x00edadad50000000 0x0000000000000000 0x00e4bffff0000000

def z262 : W := mkw 0x0a8dd61aa85092b8 0xaabe5fb8c8c6322d 0x001ffc3ff87807e0 0xffff5ffcc8e7323f

def z263 : W := mkw 0x28568a8000024304 0x402c02e001b80098 0xf01fffc0000007ff 0xf01c07e000f803f8

def z264 : W := mkw 0x3203004600887171 0x11800deff010a9b6 0xf01f03fe07ffffff 0xff04fffff018ffff

def z265 : W := mkw 0x3e03c24784cc7171 0x11ffedeff010a9b6 0x00000000000007ff 0xfffffffff00003ff

def z266 : W := mkw 0x8c10822104030000 0x006d800003294000 0xffffffffff800000 0x00ff80000fffc000

def z267 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffe0ffc1ff87f800 0x00ffa0000fffcc00

def z268 : W := mkw 0x0084100820000288 0x8800121008840209 0x001ffc3ff80007e0 0xff1b1b9c08e7023f

def z269 : W := mkw 0x2086100020004308 0x8800124008900298 0xf01fffc0000007ff 0xf01c1fe008f803f8

def z270 : W := mkw 0x0080100820000088 0x8800101008040201 0x00000000000007e0 0x0f00181c00000207

def z271 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0f81b800ff803f8

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00181b8000000000

def z273 : W := mkw 0x1080100c200020c8 0x8800101208048303 0xf000003fff8007ff 0x0f039c1f0807c3c7

def z274 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff000463f018ffff

def z275 : W := mkw 0x8d10a32146270000 0x006da00003294400 0xffff03fe07fff800 0x00e4e0000718fc00

def z276 : W := mkw 0xdfb8f33df767a4da 0x8cfffdbf5f6fd743 0xffffffffffffffff 0x0fffffffffffffc7

def z277 : W := mkw 0xf6f618ad350367de 0xccc19e570fbdc3db 0xffffffffff8007ff 0xffe39c1f0fffc3ff

def z278 : W := mkw 0x8400002104010000 0x0041800002014000 0x0000003fff800000 0x000380000007c000

def z279 : W := mkw 0x2803c24280cc5121 0x113e61e8f01028b4 0x001f03c0007ff800 0xf01c63e0f0183c38

def z280 : W := mkw 0x0084100020000208 0x8800120008800208 0x001ffc00000007e0 0xf000000008e00238

def z281 : W := mkw 0x0c00820104040000 0x006da00000000000 0x0000000000000000 0x00e4a00000000000

def z282 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff0084030018ffff

def z283 : W := mkw 0x7ad69ac4208a675d 0xd9ac1ee22db88bda 0xffffffc00787ffff 0xf0fcbfe33ff8cff8

def z284 : W := mkw 0x8400002104010000 0x0041800002014000 0xffe0000007800000 0x00e080000700c000

def z285 : W := mkw 0xad1be373c6efd121 0x117fe040a37b7cb4 0xfffffffffffff800 0xf0ffe060fffffc38

def z286 : W := mkw 0xd4a0102d350124ca 0x8c4190170e05c343 0xffe0003fff8007ff 0x0f03801f0f07c3c7

def z287 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0x0fe0fc01f8000000 0x00ffffffffe70000

def z288 : W := mkw 0x52a0100c310024da 0x8c801dbf5c048343 0x00000000000007ff 0x0f001ffff00003c7

def z289 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0xfffffffffffff800 0x00fffb9c0ffffc00

def z290 : W := mkw 0x4a90920020020418 0x88ac1c000d280240 0xffffffc0000007ff 0x00fc1c000ff803c0

def z291 : W := mkw 0x6ad79e8a281257bc 0xeaac1ff8cdbc22fd 0xffffffc0000007ff 0xfffc1ffccff803ff

def z292 : W := mkw 0x6ad6da80a042471c 0xc8be5fe84db802d8 0xffffffc0000007ff 0xf0ff5ffccff803f8

def z293 : W := mkw 0xddb8f33df767a4ca 0x8c7ff0120f6fd743 0xffffffffffffffff 0x0fffe0000fffffc7

def z294 : W := mkw 0x0a00820000000010 0x00ac0ca000000000 0x0000000000000000 0x00fcffe3f0000000

def z295 : W := mkw 0xd0a0102c310124ca 0x8c0010120e05c343 0xffe0003fff8007ff 0x0f03181c0f07c3c7

def z296 : W := mkw 0x4280100820000498 0x88801c100c040241 0xffe0003ff80007ff 0x0fe31c1c0f0703c7

def z297 : W := mkw 0x819d753aea7392a8 0xaa125318cbef762d 0xffffffffffffffe0 0xff1b5b9ccffffe3f

def z298 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe00000078007ff 0x0fe09c1f0700c3c7

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000e003f0000000

def z300 : W := mkw 0x3e038247048c7171 0x11edace7b010a9b6 0xf01f03fe07ffffff 0xffe4e463f018ffff

def z301 : W := mkw 0x62c618802000471c 0xc8801ee00c9002d8 0xf01f03c0000007ff 0xf0041fe0001803f8

def z302 : W := mkw 0x3002004400886141 0x1100004220108992 0x000000000000001f 0x00000463300001c0

def z303 : W := mkw 0x6a528a8000024514 0x40ac0ce0053800d0 0xffe003c00000001f 0x00fc1fe0071801c0

def z304 : W := mkw 0xd620002515012452 0x04c18c070601c142 0xffe000000780001f 0x00e39c1f0700c1c0

def z305 : W := mkw 0xd6a8503db541a4da 0x8cd3dc170e47d343 0xfffffc3ffff807ff 0x0ffbdc1f0fe7f3c7

def z306 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0004e00000000000

def z307 : W := mkw 0x0009441a885090a0 0x22124118c0463025 0x0000003ff8780000 0x0f1b5b9cc0073007

def z308 : W := mkw 0xf6a2102d350165da 0x8cc19c570e15c3d3 0xffff03ffff8007ff 0xffe79c7f0f1fc3ff

def z309 : W := mkw 0x6ad69a882002479c 0xc8ac1ef00dbc02d9 0xfffffffff80007ff 0xffff1ffc0fff03ff

def z310 : W := mkw 0x2e03c24384cc5131 0x11ffededf01028b4 0x001f03c0007ff800 0xf0fffffff0183c38

def z311 : W := mkw 0x8108213042218000 0x0000000002435400 0x0000003ffffff800 0x000000000007fc00

def z312 : W := mkw 0x70d718c6208a776d 0xd9001242adb8abfe 0xfffffffe07ffffff 0xff04e463fff8ffff

def z313 : W := mkw 0x7af69a8c310267de 0xccac1ef70dbc83db 0xffffffc0000007ff 0xfffc1fff0ff803ff

def z314 : W := mkw 0x94a0102d350120ca 0x8c4190170a05c303 0x0000003fff8007e0 0x0f03981f0807c207

def z315 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff03401cc8e7323f

def z316 : W := mkw 0x000d441288509220 0x22124308c0c2302c 0x001ffc3ff8780000 0xf01b4380c8e73038

def z317 : W := mkw 0xeef69aa93503479e 0xcced9ef50fbd42d9 0xffffffc1f80007ff 0xf0ff1ffc0fff03f8

def z318 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fb1ffff0000000

def z319 : W := mkw 0x3603004704887171 0x11c18c47a010a9b6 0xf01f03fe07ffffff 0xffe7fc7ff018ffff

def z320 : W := mkw 0xd7b8313d7723a4da 0x8cc19c170f6fd743 0xffffffffffffffff 0x0fe39c1f0fffffc7

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00000463f0000000

def z322 : W := mkw 0x2003004200885121 0x11000040a01028b4 0x001f03c0007ff800 0xf000000000183c38

def z323 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0x0ffffc3ff8780000 0x00fb40000fe73000

def z324 : W := mkw 0x308f545ea8d8f3e9 0xbb12535ae8d6bbbf 0xf01fffffffffffff 0xff1b5b9cc8ffffff

def z325 : W := mkw 0x6edfde9bac56d7bc 0xeafffffdddfe32fd 0xfffffffff87807ff 0xffffffffffff33ff

def z326 : W := mkw 0x8118213042238000 0x00000000036b5400 0xfffffffffffff800 0x0004e0000ffffc00

def z327 : W := mkw 0x0000000800000080 0x0000001000040001 0x0000003ff8000000 0x0f03001c00070007

def z328 : W := mkw 0x0800c20080440000 0x003e61a850000000 0x0000000000000000 0x001f7bfcf0000000

def z329 : W := mkw 0xd7a8713df765a4da 0x8cd3fc170e47d743 0xffe0003fffffffff 0x0fe3fc1f0f07ffc7

def z330 : W := mkw 0xfffefbbdf767e7de 0xccfffef70fffd7db 0xffffffffffffffff 0xffffffff0fffffff

def z331 : W := mkw 0x4080100020000408 0x880010000c000240 0xffe00000000007ff 0x000000000f0003c0

def z332 : W := mkw 0x0810820000020000 0x002c000001280000 0xffe003c000000000 0x00e4000007180000

def z333 : W := mkw 0x0a84920020000218 0x88ac1ea008800208 0x001ffc00000007e0 0xf0fc1fe008e00238

def z334 : W := mkw 0x4ad49a802002061c 0xc8ac1ea00da80248 0xffffffc000000000 0x00fc1b800ff80000

def z335 : W := mkw 0x6242088000004514 0x40800ce0041000d0 0x000000000000001f 0x00000460000001c0

def z336 : W := mkw 0x6282100020004518 0x88801c400c1002d0 0xffff03c0000007ff 0xf0e41c600f1803f8

def z337 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0x00000000000007ff 0xff04e463f00003ff

def z338 : W := mkw 0x0200400080400010 0x00924dad50000000 0x0000000000000000 0x001b5ffff0000000

def z339 : W := mkw 0xefdfffbbee77d7bc 0xeafffff8cfff76fd 0xffffffffffffffff 0xfffffffccfffffff

def z340 : W := mkw 0x0001040a081010a0 0x22000118c0042025 0x0000000000000000 0x0f00001cc0000007

def z341 : W := mkw 0x2812820000024100 0x002c004001380090 0xffffffc0000007ff 0xf0fc04600ff803f8

def z342 : W := mkw 0x0e00820104040010 0x00edaca510000000 0x0000000000000000 0x00fcbfe330000000

def z343 : W := mkw 0x2002000000004100 0x0000004000100090 0xf01f03c0000007ff 0xf0000000001803f8

def z344 : W := mkw 0x008d141a281092a8 0xaa00121088c6322d 0x001ffc3ff87807e0 0xff181b8008e7323f

def z345 : W := mkw 0x0200000000000010 0x00800c0000000000 0x0000000000000000 0x00e01c0000000000

def z346 : W := mkw 0x8d18e331c6678000 0x007fe108436b5400 0xfffffffffffff800 0x00fffb9ccffffc00

def z347 : W := mkw 0x008d541aa85092a8 0xaa12521088c6322d 0x001ffc3ff87807e0 0xff1b400008e7323f

def z348 : W := mkw 0x4284100020000618 0x88801e000c800248 0xfffffc00000007ff 0xf0f81f800fe003f8

def z349 : W := mkw 0x85186131c6678000 0x0053e000036b5400 0xfffffffffffff800 0x0003e0000ffffc00

def z350 : W := mkw 0xd0a0102c310124ca 0x8c0010120e05c343 0xffe0003fff8007ff 0x0f0084030f07c3c7

def z351 : W := mkw 0xcef49aa93503069e 0xcced9eb50fad4249 0x0fe0fc01f8000000 0x00fb1b9c0fe70000

def z352 : W := mkw 0x08548a8000020204 0x402c02a001a80008 0x0000fc0000000000 0x0018038000e00000

def z353 : W := mkw 0x28d69a802002430c 0xc82c12e009b80298 0x001fffc0000007e0 0xf01c1be008f80238

def z354 : W := mkw 0x7ed7dac7a4ce777d 0xd9ffffeffdb8abfe 0xfffffffe07ffffff 0xfffffffffff8ffff

def z355 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fcffe3fff803f8

def z356 : W := mkw 0x000d441288509220 0x22124308c0c2302c 0x001ffc0000780000 0xf01b5b9cc0e03038

def z357 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0x0000003e07ffffff 0xff00e463f000ffff

def z358 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe3181c0f07c3c7

def z359 : W := mkw 0x0001000200001020 0x0000000080002024 0x0000003e00780000 0x0f004000c0003007

def z360 : W := mkw 0x208f541aa850d3a8 0xaa125358c8d632bd 0xf01ffffff87807ff 0xff1f5ffcc8ff33ff

def z361 : W := mkw 0x099df71aea7692a8 0xaa3e7318c9ee362d 0x001ffffff87fffe0 0xff1f7b9cc8ff3e3f

def z362 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000003e000007e0 0x0f00000000000207

def z363 : W := mkw 0x9e20c22d954520d2 0x04ffedbf5205c103 0x0000003fff800000 0x0ffffffff007c007

def z364 : W := mkw 0xef52aba146274514 0x40edace0073944d0 0xffe003c00787f81f 0x00e4a4600718cdc0

def z365 : W := mkw 0x85086131c6658000 0x0053e00002435400 0xffe0003ffffff800 0x00e3e0000f07fc00

def z366 : W := mkw 0x0800820000040000 0x002c20a010000000 0x0000000000000000 0x0004206030000000

def z367 : W := mkw 0x1000000400002040 0x0000000200008102 0xf01f03fe07ffffff 0x0f04e4030018ffc7

def z368 : W := mkw 0x62c71c8a281057bc 0xea801ff8cc9422fd 0x00000000000007ff 0xff001ffcc00003ff

def z369 : W := mkw 0x6ed6da81a446471c 0xc8fffee00db802d8 0xffffffc0000007ff 0xf0ffffe00ff803f8

def z370 : W := mkw 0x94ad543fbd51b2ea 0xae53d31fcac7f32f 0x001ffc3ffff807e0 0xff1bdb9fc8e7f23f

def z371 : W := mkw 0x0008401080408000 0x0012410840421000 0x001ffc3ff8780000 0x001b5b9cc8e73000

def z372 : W := mkw 0x0c8dd61bac5492a8 0xaa7ff318c8c6322d 0x001ffc3ff87807e0 0xfffffb9cc8e7323f

def z373 : W := mkw 0x9d38e33dd767a0c2 0x047fe017036fd503 0xfffffffffffff800 0x0fffe01f0ffffc07

def z374 : W := mkw 0xdfbdf73fff77b6fa 0xaeffff1fcfeff76f 0xffffffffffffffff 0xffffff9fcfffffff

def z375 : W := mkw 0x8d98f339e6678088 0x887ff0100b6f5601 0xffffffffffffffe0 0x0ffff81c0ffffe07

def z376 : W := mkw 0xfef69aa53503675e 0xcced9ee70fb9c3da 0xffffffc0078007ff 0xf0fc9fe30ff8c3f8

def z377 : W := mkw 0x38138246008a7161 0x112c0042a138a9b6 0xfffffffe07ffffff 0xfffce463fff8ffff

def z378 : W := mkw 0x0285140a281012b8 0xaa801fbdd884222d 0x00000000000007e0 0xff001ffff000023f

def z379 : W := mkw 0x0a10820000020010 0x00ac0ca001280000 0xffffffc000000000 0x00fc1fe00ff80000

def z380 : W := mkw 0x9d18e335c667a040 0x007fe002036bd502 0xffffffffffffffff 0x0fffe4030fffffc7

def z381 : W := mkw 0xe1de39b06223c70c 0xc80012400ffb56d8 0xffffffffffffffff 0xf00000000ffffff8

def z382 : W := mkw 0x0080100020000008 0x8800100008000200 0x00000000000007e0 0x0000180008000200

def z383 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0x001ffffffffff800 0x001fe00000fffc00

def z384 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0004046000000000

def z385 : W := mkw 0x8f18e331c6678010 0x00ffeca0036b5400 0xfffffffffffff800 0x00ffffe00ffffc00

def z386 : W := mkw 0x0600400184440010 0x00d3edad50000000 0x0000000000000000 0x0003fffff0000000

def z387 : W := mkw 0xc6a010293501049a 0x8cc19c150e054241 0x0fe0003ff80007e0 0x0fe3181c0f070207

def z388 : W := mkw 0x0800c20080440000 0x003e600000000000 0x0000000000000000 0x001c600000000000

def z389 : W := mkw 0x0009401280409020 0x0012400080423024 0x001ffc3ff87807e0 0xff1b4000c8e7323f

def z390 : W := mkw 0x008c141828108288 0xaa00121008c61209 0x0000fc01f8000000 0x0000000008e70000

def z391 : W := mkw 0x6bdefb90e266c71c 0xc8be7ee00dfa16d8 0xffffffc0007fffff 0xf0fc7fe00ff83ff8

def z392 : W := mkw 0x8000002000010000 0x0000000002014000 0xffe0003fff800000 0x000000000f07c000

def z393 : W := mkw 0x8d08e331c6658000 0x007fe00002435400 0x0000003ffffff800 0x00ffe0000007fc00

def z394 : W := mkw 0xd6a1106f358934fb 0x9dc19c17ae05eb67 0xffe0003fffffffff 0x0fe3fc1fff07ffc7

def z395 : W := mkw 0xdf30a32557272452 0x04edac070729c542 0xffe003c00787f81f 0x00e4a4030718cdc0

def z396 : W := mkw 0xfef79aef358b77ff 0xdded9ef7afbdebff 0xffffffffffffffff 0xffffffffffffffff

def z397 : W := mkw 0x72e6188c310067de 0xcc801ef70c9483db 0x00000000000007ff 0xff001fff000003ff

def z398 : W := mkw 0x8c00c22184450000 0x007fe00002014000 0xffe0003fff800000 0x00ffe0000f07c000

def z399 : W := mkw 0x0600000104000010 0x00c18dad50000000 0x0000000000000000 0x00e39ffff0000000

def z400 : W := mkw 0x1001004600883061 0x11000002a000a926 0x0000000000000000 0x0f000003f0000007

def z401 : W := mkw 0x1001004600883061 0x11000002a000a926 0x0000003e07fff800 0x0f0000000000fc07

def z402 : W := mkw 0x68d69a802002470c 0xc82c12400db802d8 0xffffffc0000007ff 0xf0fc00000ff803f8

def z403 : W := mkw 0x8d19e333c6679020 0x007fe000836b7424 0xffffffffffffffe0 0xffffe000cffffe3f

def z404 : W := mkw 0x2003004200885121 0x11000040a01028b4 0x001f03fe007fffe0 0xff046060f0183e3f

def z405 : W := mkw 0x9420402d954520c2 0x0453e11f5205c103 0x0000003fff800000 0x0f03e01ff007c007

def z406 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1b1b9c08e7323f

def z407 : W := mkw 0x0200000000000010 0x00800ca510000000 0x0000000000000000 0x0000046330000000

def z408 : W := mkw 0x2003000200005120 0x00000040801020b4 0xf01f03fe007807ff 0xff044460c01833ff

def z409 : W := mkw 0x60c618802000470c 0xc80012400c9002d8 0x00000000000007ff 0xf0000000000003f8

def z410 : W := mkw 0x0089541aa85090a8 0xaa125118c8463225 0x0000003ff87807e0 0x0f03581cc8073207

def z411 : W := mkw 0x4280100020000418 0x88801c000c000240 0x00000000000007ff 0x00001c00000003c0

def z412 : W := mkw 0xfea3d26fb5cd75fb 0x9dfffdfffe15ebf7 0xffff03ffffffffff 0xffffffffff1fffff

def z413 : W := mkw 0x95096177c6edb061 0x1153e002a243fd26 0x0000003ffffff800 0x0f03e003f007fc07

def z414 : W := mkw 0x2e02c20184444110 0x00ffeded50100090 0xf01f03c0000007ff 0xf0fffffff01803f8

def z415 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0e404600ff803f8

def z416 : W := mkw 0x0085540aa85012a8 0xaa125318c884222d 0x00000000000007e0 0xff1b5b9cc000023f

def z417 : W := mkw 0xd6a0502db54124da 0x8cd3dd1f4e05c343 0xffe0003fff8007ff 0x0ffbdf9fcf07c3c7

def z418 : W := mkw 0xf623006715897573 0x15c18c47a611e9f6 0xffff03fe07ffffff 0xffe4e463f718ffff

def z419 : W := mkw 0x0084100020000208 0x8800120008800208 0x00000000000007e0 0xf0001b8000000238

def z420 : W := mkw 0x089dd61aa85292a8 0xaa3e5318c9ee322d 0xfffffffff87807e0 0xffff5b9ccfff323f

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0xf00003c00787f800 0x0004a0000018cc00

def z422 : W := mkw 0x0000400080400000 0x0012400000000000 0x0000000000000000 0x001b400000000000

def z423 : W := mkw 0x0e00c20184440010 0x00ffeca510000000 0x0000000000000000 0x00ffe46330000000

def z424 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0x001f03fe07fff800 0xff04e063f018fc3f

def z425 : W := mkw 0x0085140a281012a8 0xaa001318c884222d 0x0000003ff80007e0 0xff031b9cc807023f

def z426 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fb5b9cc0000000

def z427 : W := mkw 0x38578ac6008a7365 0x512c02e2a1b8a9be 0xf01ffffe07ffffff 0xff1ce7e3f0f8ffff

def z428 : W := mkw 0x0600400184400010 0x00d3cd0d40000000 0x0000000000000000 0x00fbdf9fc0000000

def z429 : W := mkw 0x1000000400002040 0x0000000200008102 0xf000003e078007ff 0x0f0000000000c3c7

def z430 : W := mkw 0xd2a0102c310124da 0x8c801c170e05c343 0xffe0003fff8007ff 0x0f001c1f0f07c3c7

def z431 : W := mkw 0x0084100020000208 0x8800120008800208 0x0000fc0000000000 0x00181b8008e00000

def z432 : W := mkw 0x0e8dd61bac5492b8 0xaaffffbdd8c6322d 0x001ffc3ff87807e0 0xfffb5b9cc8e7323f

def z433 : W := mkw 0xc0a010283101048a 0x8c0010100e054241 0x0fe00001f8000000 0x000000000f070000

def z434 : W := mkw 0x3087144e289873e9 0xbb00135ae894abbf 0xf01f03fe07ffffff 0xff04fffff018ffff

def z435 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000003ff8000000 0x0003000008070000

def z436 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00ffbfff30000000

def z437 : W := mkw 0x0e09c61b8c5490b0 0x22ffedbdd0463025 0x0000003ff8780000 0x0ffffffff0073007

def z438 : W := mkw 0x62d618802002471c 0xc8801e400db802d8 0xffffffc0000007ff 0xf0e01c000ff803f8

def z439 : W := mkw 0x0918e310c2668000 0x003e6000016a1400 0x0000fc0000000000 0x0018000000e00000

def z440 : W := mkw 0x0e10c20184460010 0x00ffedad51280000 0xffffffc000000000 0x00fffffffff80000

def z441 : W := mkw 0x2002000000004100 0x0000004000100090 0x00000000000007ff 0xf0000460000003f8

def z442 : W := mkw 0x4ad49a802002061c 0xc8ac1ea00da80248 0x0fe0fc0000000000 0x00fc1fe00fe00000

def z443 : W := mkw 0x8d9cf331e6678208 0x887ff2000beb5608 0xffffffffffffffe0 0xf0fffb800ffffe38

def z444 : W := mkw 0x6ad79a822002573c 0xc8ac1ee08db822fc 0xfffffffe007807ff 0xfffc5fe0cff833ff

def z445 : W := mkw 0xd0ad543eb951b6ea 0xae12531acec7f36f 0xfffffc3ffff807ff 0xff1b5b9ccfe7f3ff

def z446 : W := mkw 0x0e85d60bac5412b8 0xaaffffbdd884222d 0x00000000000007e0 0xfffffffff000023f

def z447 : W := mkw 0x208f545aa8d8d3a9 0xbb125358e8d63abd 0x001ffffff87fffe0 0xff1f7bfcf8ff3e3f

def z448 : W := mkw 0x28dfde9aa852d3ac 0xea3e53f8c9fe32bd 0x001ffffff87807e0 0xff1f5bfcc8ff323f

def z449 : W := mkw 0xb423006f158971e3 0x15418057a215e9b7 0xf01f03ffffffffff 0xff07e47ff01fffff

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0xf000003e07800000 0x000080000000c000

def z451 : W := mkw 0x5220000411002452 0x04800c0704008142 0x000000000000001f 0x00000403000001c0

def z452 : W := mkw 0x291be352c2eed121 0x113e6040a17a3cb4 0x001fffc0007ff800 0xf01c6060f0f83c38

def z453 : W := mkw 0x3087104620887369 0x99001242a890abbe 0xf01ffffe07ffffff 0xff1cffe3f8f8ffff

def z454 : W := mkw 0x8420002915010082 0x0441801502054001 0x00000001f8000000 0x0003001c00070000

def z455 : W := mkw 0xd0ad143e3911b6ea 0xae0012128ec7f36f 0xfffffc3ffff807ff 0xff0000000fe7f3ff

def z456 : W := mkw 0x0c00c20184440000 0x007fe1ad50000000 0x0000000000000000 0x001fe3fff0000000

def z457 : W := mkw 0x8400002104010000 0x0041800002014000 0x0fe00001f8000000 0x00e300000f070000

def z458 : W := mkw 0xc6ad543bbd5196ba 0xaed3df1dcec7726d 0x0ffffc3ff87807e0 0xfffb5b9ccfe7323f

def z459 : W := mkw 0x0e80d209a4440098 0x88fffdbd58040201 0x0000003ff80007e0 0x0ffffffff8070207

def z460 : W := mkw 0x0810820000020000 0x002c000001280000 0x001fffc000000000 0x001c000000f80000

def z461 : W := mkw 0x3083104e208871e9 0x99001052a814abb7 0xf01f03ffffffffff 0xff07fc7ff81fffff

def z462 : W := mkw 0x6a568a8000024714 0x40ac0ee005b800d8 0xffffffc00000001f 0xf0fc07e007f801f8

def z463 : W := mkw 0x1001000600003060 0x000000028000a126 0xf01f003e07f807ff 0xff00c403c000f3ff

def z464 : W := mkw 0x6e528a8104064514 0x40edace5153800d0 0xffe003c00000001f 0x00e4a463371801c0

def z465 : W := mkw 0x8509653bce7590a0 0x2253e118c2477425 0x0000003ffffff800 0x0f03e01cc007fc07

def z466 : W := mkw 0x42c418802000061c 0xc8801ea00c800248 0x0000000000000000 0x00001b8000000000

def z467 : W := mkw 0xf6a3106f358975fb 0x9dc19c57ae15ebf7 0xffff03ffffffffff 0xffe39c1f0f1fffff

def z468 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x0000fc3ff8780000 0x0f1b5b9cc8e73007

def z469 : W := mkw 0x295eeb90c266c304 0x403e62e001fa1498 0x001fffc0007ff800 0xf01c63e000f83c38

def z470 : W := mkw 0xefdefbb1e667c71c 0xc8fffee00ffb56d8 0xffffffc1f80007ff 0xf0ff1fe00fff03f8

def z471 : W := mkw 0x0085140a281012a8 0xaa001318c884222d 0x001f003e007807e0 0xff005b9cc000323f

def z472 : W := mkw 0x008c5418a8508288 0xaa12531848c61209 0x0000fc3ff80007e0 0x0f1b1b9c08e70207

def z473 : W := mkw 0xbd1be377c6eff161 0x117fe042a37bfdb6 0xffffffffffffffff 0xffffe0000fffffff

def z474 : W := mkw 0x0e00820104040010 0x00edaca510000000 0x0000000000000000 0x00e0000000000000

def z475 : W := mkw 0x0600000104000010 0x00c18c0500000000 0x0000000000000000 0x00e0840300000000

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0x001f003e00780000 0x0000400000003000

def z477 : W := mkw 0x3002000400006140 0x0000004200108192 0xf01f03fe078007ff 0xff0484630018c3ff

def z478 : W := mkw 0x4a508a8000020414 0x40ac0ca005280040 0x0fe0000000000000 0x00e0000007000000

def z479 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffffffc007fff800 0x00fce00007f8fc00

def z480 : W := mkw 0x8f9df73bee7792b8 0xaaffffbddbef762d 0xffffffffffffffe0 0xfffffffffffffe3f

def z481 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe00001ff80001f 0x00e39c1f0f07c1c0

def z482 : W := mkw 0xcfdcfbb1e667861c 0xc8fffea00feb5648 0xfffffffffffff800 0x00fffb800ffffc00

def z483 : W := mkw 0x1e01c24784cc3071 0x11ffedaff000a926 0x0000003e07fff800 0x0ffffffff000fc07

def z484 : W := mkw 0x2003004200885121 0x11000040a01028b4 0xf01f03fe07fff800 0xf004e060f018fc38

def z485 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0003181c00000000

def z486 : W := mkw 0x0000400080400000 0x0012410840000000 0x0000000000000000 0x001ffffff0000000

def z487 : W := mkw 0x4200000000000410 0x00800c0004000040 0xffe000000000001f 0x00e00400070001c0

def z488 : W := mkw 0x52a5140e391036fa 0xae801f1fcc84a36f 0x00000000000007ff 0xff001f9fc00003ff

def z489 : W := mkw 0x6adfde92a852d73c 0xeabe5fe8cdfa32fc 0xffffffc0007807ff 0xf0fc5fe0cff833f8

def z490 : W := mkw 0x8408403184418000 0x0053c00002435000 0xfffffc3ffff80000 0x00fbc0000fe7f000

def z491 : W := mkw 0xdef49aad350326de 0xcced9eb70fadc34b 0xffe0fc3fff8007ff 0x0ffb9f9f0fe7c3c7

def z492 : W := mkw 0x0894920020020208 0x882c120009a80208 0xffffffc0000007e0 0xf0fc1b800ff80238

def z493 : W := mkw 0x1020000c110020c2 0x0400001700048103 0x0000000000000000 0x0f00001f00000007

def z494 : W := mkw 0x9429443f9d51b0e2 0x2653c11fc247f127 0x0000003ffff80000 0x0f03c01fc007f007

def z495 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffe0ffc00000001f 0x00fc1fe00ff801c0

def z496 : W := mkw 0x108d545ea8d8b2e9 0xbb12531ae8c6bb2f 0x001ffc3fffffffe0 0xff1bfb9ff8e7fe3f

def z497 : W := mkw 0x3e028245048c6151 0x11edace730108992 0xf00003c00787f81f 0x00e4a4633018cdc0

def z498 : W := mkw 0x4280100020000418 0x88801c000c000240 0x0fe0000000000000 0x00e018000f000000

def z499 : W := mkw 0x858d753bee7592a8 0xaa53f318cac7762d 0x001ffc3fffffffe0 0xff1bfb9cc8e7fe3f

def z500 : W := mkw 0x108d541ea850b2e8 0xaa12531ac8c6b32f 0xf01ffc3ffff807ff 0xff1bdf9fc8e7f3ff

def z501 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0x001f03c0007fffff 0xff046463f0183fff

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0xf01f03fe07fff800 0x0004e463f018fc00

def z503 : W := mkw 0xdea0d22db54524da 0x8cfffdbf5e05c343 0xffe0003fff8007ff 0x0ffb9f9f0f07c3c7

def z504 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0x0000003fff8007ff 0x0f039c1f0007c3c7

def z505 : W := mkw 0xf6a2106d358965db 0x9dc19c572e15cbd3 0xffe003ffff87ffff 0x0fe7bc7f3f1fcfc7

def z506 : W := mkw 0x0000000000000000 0x0000010840000000 0x0000000000000000 0x00001b9cc0000000

def z507 : W := mkw 0x6ad69a802002471c 0xc8ac1fed5db802d8 0xffffffc0000007ff 0xf0fc1ffffff803f8

def z508 : W := mkw 0x6ad79ac2208a573d 0xd9ac1ee0adb82afc 0xffffffc0007fffff 0xf0fc7fe0fff83ff8

def z509 : W := mkw 0xb11b217642abf161 0x11000042a37bfdb6 0xffffffffffffffff 0xff0000000fffffff

def z510 : W := mkw 0x0400400184440000 0x0053e10d50000000 0x0000000000000000 0x0003001c00000000

def z511 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffffffc1f8000000 0x00ff00000fff0000

def z512 : W := mkw 0xad1ae331c667c100 0x007fe040037b5490 0xffffffffffffffff 0xf0ffe4600ffffff8

def z513 : W := mkw 0x2a568a8000024314 0x40ac0ee001b80098 0x001fffc000000000 0xf0fc1fe000f80038

def z514 : W := mkw 0x8918e330c2678000 0x003e6000036b5400 0xfffffffffffff800 0x001c60000ffffc00

def z515 : W := mkw 0x0e00820104040010 0x00edaca510000000 0x0000000000000000 0x00e4e463f0000000

def z516 : W := mkw 0x1e00c20584442050 0x00ffedaf50008102 0xf000003e078007ff 0x0ffffffff000c3c7

def z517 : W := mkw 0xfe728aa515036556 0x44ed8ce70739c1d2 0xffe003c00780001f 0x00e484630718c1c0

def z518 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fffb9c00000000

def z519 : W := mkw 0x0e01c20384441030 0x00ffedadd0002024 0x001f003e007807e0 0xfffffffff000323f

def z520 : W := mkw 0x62d618802002471c 0xc8801ee00db802d8 0xffffffc0000007ff 0xf0001fe00ff803f8

def z521 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff04a4633018ffff

def z522 : W := mkw 0xdea0922d350124da 0x8ced9cb70e05c343 0xffe0003fff8007ff 0x0fff9fff0f07c3c7

def z523 : W := mkw 0x0e8cd619ac548298 0xaaffffbd58c61209 0x0000fc01f8000000 0x00fffffff8e70000

def z524 : W := mkw 0x8f18e331c6678010 0x00ffec05036b5400 0xfffffffffffff800 0x00fffc1f0ffffc00

def z525 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00004000c0000000

def z526 : W := mkw 0xbd9ff77feefff3e9 0xbb7ff35aebffffbf 0xffffffffffffffff 0xffffffffffffffff

def z527 : W := mkw 0x0001004200881021 0x11000000a0002824 0x00000000007ff800 0x00006000f0003c00

def z528 : W := mkw 0x0918e310c2668000 0x003e6000016a1400 0xf01ffffe07fff800 0x001ce00000f8fc00

def z529 : W := mkw 0x9620002d150120d2 0x04c18c170205c103 0x0000003fff800000 0x0fe39c1f0007c007

def z530 : W := mkw 0x8110212042230000 0x0000000003294400 0xffe003c00787f800 0x000000000718cc00

def z531 : W := mkw 0xb11b217642abf161 0x11000042a37bfdb6 0xffffffffffffffff 0xff04e463ffffffff

def z532 : W := mkw 0x8f10e321c6670010 0x00ffedad53294400 0xffe003c00787f800 0x00fffffff718cc00

def z533 : W := mkw 0xefdefbb1e667c71c 0xc8ffffed5ffb56d8 0xffffffffffffffff 0xf0fffffffffffff8

def z534 : W := mkw 0x8d10e321c6670000 0x007fe00003294400 0xffe003c00787f800 0x00ffe0000718cc00

def z535 : W := mkw 0xd020002411012442 0x040000020601c142 0xffe000000780001f 0x000000000700c1c0

def z536 : W := mkw 0x0008441888508080 0x2212411840461001 0x00000001f8000000 0x0003001c00070000

def z537 : W := mkw 0x00805008a0400088 0x8812511848040201 0x0000003ff80007e0 0x0f1b5b9cc8070207

def z538 : W := mkw 0x0c00c20184440000 0x007fe1a850000000 0x0000000000000000 0x00ffe3e0f0000000

def z539 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf00003c00787ffff 0xff04a463f018cfff

def z540 : W := mkw 0x0001000200001020 0x0000000080002024 0x001f003e007807e0 0xff0000000000323f

def z541 : W := mkw 0x8d10a32146270000 0x006da00003294400 0xffffffc00787f800 0x00fca0000ff8cc00

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0x001f03c0007ff800 0x0004600000183c00

def z543 : W := mkw 0x0400400184440000 0x0053e10d50000000 0x0000000000000000 0x0007e47ff0000000

def z544 : W := mkw 0x0000400080440000 0x0012610850000000 0x0000000000000000 0x00006000f0000000

def z545 : W := mkw 0x0001000200001020 0x0000000080002024 0x001f003e007807e0 0xff04e463f000323f

def z546 : W := mkw 0x9420002515012042 0x044180070201c102 0x0000000007800000 0x000080030000c000

def z547 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x0000003ff87807e0 0xff035b9cc007323f

def z548 : W := mkw 0x1001004600883061 0x11000002a000a926 0x001f003e07ffffe0 0xff00e003f000fe3f

def z549 : W := mkw 0xd620002515012452 0x04c18c070601c142 0xffe0003e078007ff 0x0fe084030700c3c7

def z550 : W := mkw 0xd6a4102d350126da 0x8cc19e170e85c34b 0xfffffc3fff8007ff 0xfffb9f9f0fe7c3ff

def z551 : W := mkw 0x62cf5c9aa850d7bc 0xea925ff8ccd632fd 0x001ffc3ff87807ff 0xff1b5ffcc8e733ff

def z552 : W := mkw 0x1600000504002050 0x00c18c0700008102 0xf000003e078007ff 0x0fe39c1f0000c3c7

def z553 : W := mkw 0xeddefbb1e667c70c 0xc87ff2400ffb56d8 0xffffffffffffffff 0xf0ffe0000ffffff8

def z554 : W := mkw 0x0008401080408000 0x0012400000421000 0x0000003ff8780000 0x0003400000073000

def z555 : W := mkw 0x088dd61aa85492a8 0xaa3e73b8d8c6322d 0x001ffc3ff87807e0 0xff1f7bfcf8e7323f

def z556 : W := mkw 0x0e08c21184448010 0x00ffedad50421000 0x001ffc3ff8780000 0x00fffffff8e73000

def z557 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0000000000007ff 0x00000400000003c0

def z558 : W := mkw 0x6adede98a852c79c 0xeabe5ff84dfe12d9 0xffffffc1f80007ff 0xf0ff1ffc0fff03f8

def z559 : W := mkw 0xbd13a36746af7161 0x116da042a339edb6 0xffff03fe07ffffff 0xffe4e463f718ffff

def z560 : W := mkw 0x2003004200885121 0x11000040a01028b4 0xf01f03c0007fffff 0xf0046460f0183ff8

def z561 : W := mkw 0x3203004600887171 0x11800deff010a9b6 0x00000000000007ff 0xff001ffff00003ff

def z562 : W := mkw 0xffdffbf7e6eff77d 0xd9fffee2affbfffe 0xffffffffffffffff 0xffffffe3ffffffff

def z563 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf00003fe07fff81f 0x0f04e463f018fdc7

def z564 : W := mkw 0x0800c20080440000 0x003e61a850000000 0x0000000000000000 0x0018038000000000

def z565 : W := mkw 0x008d141a281092a8 0xaa00121088c6322d 0x001ffc3ff87807e0 0xff03181c08e7323f

def z566 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0x0fffffc1f87ff800 0x00ff60000fff3c00

def z567 : W := mkw 0x7ad79ac6208a777d 0xd9ac1ee2adb8abfe 0xffffffc0000007ff 0xfffc1fe3fff803ff

def z568 : W := mkw 0x0200000000000010 0x00800ca000000000 0x0000000000000000 0x00001fe000000000

def z569 : W := mkw 0xf6a3106f358975fb 0x9dc19c57ae15ebf7 0xffe0003fff8007ff 0xffe39c7fff07c3ff

def z570 : W := mkw 0x068d541bac5092b8 0xaad3df1dc8c6322d 0x001ffc3ff87807e0 0xfffbdf9fc8e7323f

def z571 : W := mkw 0x68d69a802002470c 0xc82c12e00db802d8 0xffffffc0000007ff 0xf01c03e00ff803f8

def z572 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0x001fffc0000007ff 0xf01c1fe000f803f8

def z573 : W := mkw 0x0000400080400000 0x0012410840000000 0x0000000000000000 0x001b1b9c00000000

def z574 : W := mkw 0x0009441288509020 0x22124108c0423024 0x0000000000780000 0x00004000c0003000

def z575 : W := mkw 0x0810820000020000 0x002c000001280000 0x0fe0fc0000000000 0x00f800000fe00000

def z576 : W := mkw 0x9420002d150120c2 0x044180170205c103 0xf000003fff8007ff 0x0f03841f0007c3c7

def z577 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0x00000000000007ff 0xff000000000003ff

def z578 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03c007fff81f 0xf004e463f018fdf8

def z579 : W := mkw 0x0400000104000000 0x0041800500000000 0x0000000000000000 0x0003801f00000000

def z580 : W := mkw 0x091de712ca769220 0x223e6308c1ea342c 0x001fffc0007ff800 0xf01c6380c0f83c38

def z581 : W := mkw 0x008c5418a8508288 0xaa12531848c61209 0x001ffc3ff8780000 0x001b5b9c08e73000

def z582 : W := mkw 0x0005040208101220 0x22000308c080202c 0x0000000000000000 0xf0000380c0000038

def z583 : W := mkw 0x0e00c20184440010 0x00ffeca000000000 0x0000000000000000 0x00ffffe000000000

def z584 : W := mkw 0x4a80920020000418 0x88ac1ca00c000240 0xffe00000000007ff 0x00fc1fe00f0003c0

def z585 : W := mkw 0x1001004600883061 0x11000002a000a926 0xf000003e07ffffff 0x0f00e403f000ffc7

def z586 : W := mkw 0x6ed69a812406471c 0xc8edbee51db802d8 0xffffffc0000007ff 0xf0fcbfe33ff803f8

def z587 : W := mkw 0x8d9df73bee7792a8 0xaa7ff318cbef762d 0x0ffffc3ff87807e0 0xfffb5b9ccfe7323f

def z588 : W := mkw 0x0c10c20184460000 0x007fe00001280000 0xffffffc000000000 0x00ffe0000ff80000

def z589 : W := mkw 0x60d618802002470c 0xc80012400db802d8 0xffffffc0000007ff 0xf0181b800ff803f8

def z590 : W := mkw 0xebdebbb06223c71c 0xc8ac1ee00ffb56d8 0xffffffffffffffff 0xf0fc1fe00ffffff8

def z591 : W := mkw 0x0e84d201a4440218 0x88ffffad58800208 0x001ffc00000007e0 0xf0fffffff8e00238

def z592 : W := mkw 0xd6a9543fbd51b4fa 0xaed3dd1fce47f367 0xffe0003ffff807ff 0x0fe3dc1fcf07f3c7

def z593 : W := mkw 0xfeffdebfbd53f7fe 0xeeffdfffcffff3ff 0xfffffffffff807ff 0xffffdfffcffff3ff

def z594 : W := mkw 0x70d718c6208a776d 0xd9001242adb8abfe 0xfffffffe07ffffff 0xff0000000ff8ffff

def z595 : W := mkw 0x00845000a0400208 0x8812530848800208 0x001ffc00000007e0 0xf01b5b9cc8e00238

def z596 : W := mkw 0xdea0d22db54524da 0x8cfffc170e05c343 0xffe0003fff8007ff 0x0ffffc1f0f07c3c7

def z597 : W := mkw 0x2002000000004100 0x0000004000100090 0x001f03c000000000 0xf004006000180038

def z598 : W := mkw 0x85086131c6658000 0x0053e00002435400 0x00000001f8000000 0x0003000000070000

def z599 : W := mkw 0x0000400080400000 0x0012410840000000 0x0000000000000000 0x00184380c0000000

def z600 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00e7e47ff0000000

def z601 : W := mkw 0x0409441b8c5490a0 0x2253e11dd0463025 0x0000003ff8780000 0x0f03e01ff0073007

def z602 : W := mkw 0x0800820000000000 0x002c00a000000000 0x0000000000000000 0x001c03e000000000

def z603 : W := mkw 0x6ec6da81a444471c 0xc8ffffed5c9002d8 0x00000000000007ff 0xf0fffffff00003f8

def z604 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000840300000000

def z605 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffe003c0000007ff 0xf0e41fe0071803f8

def z606 : W := mkw 0xcfdcfbb1e667861c 0xc8fffea00feb5648 0x0fe0fc01f8000000 0x00fb1b800fe70000

def z607 : W := mkw 0x60d618802002470c 0xc80012400db802d8 0xffffffc0000007ff 0xf00404600ff803f8

def z608 : W := mkw 0x8400002104010000 0x0041800002014000 0xffff03fffffff800 0x00e7e0000f1ffc00

def z609 : W := mkw 0xd6a010253501245a 0x8cc19c070e01c342 0xffe00000078007ff 0x00e09c030f00c3c0

def z610 : W := mkw 0x6ad6da80a046471c 0xc8be7fe85db802d8 0xffffffc0000007ff 0xf0fc7fe0fff803f8

def z611 : W := mkw 0x6e52ca8184464514 0x40ffeded553800d0 0xffe003c00000001f 0x00fffffff71801c0

def z612 : W := mkw 0x3002004400886141 0x1100004220108992 0xf01f03c00787ffff 0xf004a4633018cff8

def z613 : W := mkw 0x000c441088508200 0x2212430840c21008 0x0000fc0000000000 0x0018038000e00000

def z614 : W := mkw 0x008c5418a8508288 0xaa12531848c61209 0x0000fc01f8000000 0x001b5b9cc8e70000

def z615 : W := mkw 0xc620002115010412 0x04c18c0506014040 0x0fe0000000000000 0x00e0000007000000

def z616 : W := mkw 0x0081100a200010a8 0x8800101088042225 0x001f003ff87807e0 0xff03581cc807323f

def z617 : W := mkw 0x0400400184440000 0x0053e10d50000000 0x0000000000000000 0x001bfb9ff0000000

def z618 : W := mkw 0x1000000400002040 0x0000000200008102 0x0000003e07800000 0x0f0080030000c007

def z619 : W := mkw 0x3087144e289873e9 0xbb00135ae894abbf 0x00000000000007ff 0xff001ffff00003ff

def z620 : W := mkw 0x0918e310c2668000 0x003e6000016a1400 0x001ffffff87ff800 0x001f600008ff3c00

def z621 : W := mkw 0x8500212146250000 0x0041a00002014400 0x000000000787f800 0x0000a0000000cc00

def z622 : W := mkw 0x9528613dd765a0c2 0x0453e0170247d503 0x0000003ffffff800 0x0f03e01f0007fc07

def z623 : W := mkw 0xc6a010293501049a 0x8cc19c150e054241 0xffe00001f80007ff 0x00e31c1c0f0703c0

def z624 : W := mkw 0x3002004400886141 0x1100004220108992 0xf01f03fe07fff81f 0x0004e4633018fdc0

def z625 : W := mkw 0x3c03c24784cc7161 0x117fe042a010a9b6 0xf01f03fe07ffffff 0xffffe463f018ffff

def z626 : W := mkw 0x56a0100d350024da 0x8cc19c170c048343 0x00000000000007ff 0x0fe39c1f000003c7

def z627 : W := mkw 0x81186130c2638000 0x00124000036b5400 0xfffffffffffff800 0x001b40000ffffc00

def z628 : W := mkw 0x0c08c21184448000 0x007fe00000421000 0x001ffc3ff8780000 0x00ffe00008e73000

def z629 : W := mkw 0x28568a8000024304 0x402c02e001b80098 0xffffffc000000000 0xf0fc03e00ff80038

def z630 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0x0fffffc000000000 0xf0fc1be00ff80038

def z631 : W := mkw 0x8d19e73bce7790a0 0x227fe118c36f7425 0xfffffffffffff800 0x0fffe01ccffffc07

def z632 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0x001f003e007807ff 0xff004463f00033ff

def z633 : W := mkw 0x8d18a33146278000 0x006da000036b5400 0xfffffffffffff800 0x00e4a0000ffffc00

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0xffe0000000000000 0x00e000000f000000

def z635 : W := mkw 0x72c718c62088777d 0xd9801ee2ac90abfe 0x00000000000007ff 0xff001fe3f00003ff

def z636 : W := mkw 0x0009041a081090a0 0x2200001080463025 0x0000003ff8780000 0x0f00000000073007

def z637 : W := mkw 0x0e0dc6138c549230 0x22ffefadd0c2302c 0x001ffc0000780000 0xf0fffffff0e03038

def z638 : W := mkw 0x3002004400886141 0x1100004220108992 0xf00003c00787f81f 0x0004e463f018cdc0

def z639 : W := mkw 0x308f145e2898f3e9 0xbb001252a8d6bbbf 0xf01fffffffffffff 0xff04e463f8ffffff

def z640 : W := mkw 0x42a010083100049a 0x8c801c150c040241 0x0000000000000000 0x0000181c00000000

def z641 : W := mkw 0x52ad541eb950b6fa 0xae925f1fccc6b36f 0x001ffc3ff87807ff 0xff1b5f9fc8e733ff

def z642 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00ff7bfcf0000000

def z643 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0x0fe0fc3ffffff800 0x00fbe0000fe7fc00

def z644 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff004000c018ffff

def z645 : W := mkw 0x00885018a0408088 0x8812501008461201 0x001ffc3ff87807e0 0x0f1b581c08e73207

def z646 : W := mkw 0x0400000104040000 0x0041a00510000000 0x0000000000000000 0x0000a00330000000

def z647 : W := mkw 0x5ea0d20db54424da 0x8cfffdbf5c048343 0x00000000000007ff 0x0ffffffff00003c7

def z648 : W := mkw 0xdeadd63fbd55b6fa 0xaeffffbfdec7f36f 0xfffffc3ffff807ff 0xffffffffffe7f3ff

def z649 : W := mkw 0x0001000200001020 0x0000000080002024 0x00000000000007e0 0xff000000c000023f

def z650 : W := mkw 0x4ed4da81a446061c 0xc8ffffad5da80248 0x0fe0fc0000000000 0x00ffffffffe00000

def z651 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffe003fffffff800 0x00e7e000071ffc00

def z652 : W := mkw 0x52a0100c310024da 0x8c801c170c048343 0x0000003ff80007ff 0x0f031c1f080703c7

def z653 : W := mkw 0xdeb0922d350324da 0x8ced9c170f2dc343 0xffffffffff8007ff 0x0fff9c1f0fffc3c7

def z654 : W := mkw 0x3e02c24584cc6151 0x11ffedef70108992 0xf00003c00787f81f 0x00fffffff018cdc0

def z655 : W := mkw 0x0918e310c2668000 0x003e6000016a1400 0xffffffc0007ff800 0x00fc60000ff83c00

def z656 : W := mkw 0xef5aebb1c667c514 0x40ffece0077b54d0 0xfffffffffffff81f 0x00ffe4600ffffdc0

def z657 : W := mkw 0x3803c24680cc7161 0x113e61eaf010a9b6 0xf01f03fe07ffffff 0xff1ce7e3f018ffff

def z658 : W := mkw 0xf0a3106e318975eb 0x9d001052ae15ebf7 0xffff03ffffffffff 0xff04e463ff1fffff

def z659 : W := mkw 0x008d141a281092a8 0xaa00121088c6322d 0x001ffc3ff87807e0 0xff004000c8e7323f

def z660 : W := mkw 0x0800c20080440000 0x003e61a850000000 0x0000000000000000 0x001ce7e3f0000000

def z661 : W := mkw 0xc6ac5439bd51869a 0xaed3df1d4ec75249 0x0fe0fc01f8000000 0x00fb1b9c0fe70000

def z662 : W := mkw 0x0e00820104040010 0x00edaca510000000 0x0000000000000000 0x00e7bc7f30000000

def z663 : W := mkw 0x4ad49a802002061c 0xc8ac1ea00da80248 0xffe0fc00000007ff 0x00f81f800fe003c0

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0xf01f03fe07fff800 0x000000000018fc00

def z665 : W := mkw 0x7adfdedea8daf7fd 0xfbbe5ffaedfebbff 0xffffffffffffffff 0xffffffffffffffff

def z666 : W := mkw 0x8d9cf739ee778288 0xaa7ff3184bef5609 0xfffffffffffff800 0x00fffb9c0ffffc00

def z667 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fbfb9ff0000000

def z668 : W := mkw 0x3002004400886141 0x1100004220108992 0xf00003fe0787ffff 0x0f04a4633018cfc7

def z669 : W := mkw 0xd1b8313c7323a4ca 0x8c0010120f6fd743 0xffffffffffffffff 0x0f0000000fffffc7

def z670 : W := mkw 0x4addde9aa85296bc 0xeabe5fb8cdee326d 0x0ffffc3ff87807e0 0xfffb5b9ccfe7323f

def z671 : W := mkw 0x0001000200001020 0x0000000080002024 0x001f000000780000 0xf0004000c0003038

def z672 : W := mkw 0x3003404680c87161 0x1112414ae010a9b6 0xf01f03fe07ffffff 0xff1ffffff018ffff

def z673 : W := mkw 0xbd12a36546af6141 0x116da0422339cd92 0xffe003c00787f81f 0x00e4a4633718cdc0

def z674 : W := mkw 0xde20822515052452 0x04edaca71601c142 0xffe000000780001f 0x00e4a4633700c1c0

def z675 : W := mkw 0x0818c21080428000 0x003e4000016a1000 0xfffffffff8780000 0x00ff40000fff3000

def z676 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffe0fc3fff800000 0x00fb80000fe7c000

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x001f0000000007e0 0xf000000000000238

def z678 : W := mkw 0x428d541aa85096b8 0xaa925f18ccc6326d 0xfffffc3ff87807ff 0xfffb5f9ccfe733ff

def z679 : W := mkw 0xdfb0b32d772724da 0x8cedbc170f2dc743 0xffe003ffff87ffff 0x0fe7bc1f0f1fcfc7

def z680 : W := mkw 0x2a02820000004110 0x00ac0ce000100090 0xf01f03c0000007ff 0xf0fc1fe0001803f8

def z681 : W := mkw 0x0085140a281012a8 0xaa001318c884222d 0x001ffc00000007e0 0xff181b9cc8e0023f

def z682 : W := mkw 0xb50b6177c6edf161 0x1153e042a253fdb6 0xf01f03ffffffffff 0xff07e463f01fffff

def z683 : W := mkw 0x0c00c20184440000 0x007fe00000000000 0x0000000000000000 0x00fb000000000000

def z684 : W := mkw 0x1000000400002040 0x0000000200008102 0x00000000000007ff 0x0f000403000003c7

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x001ffc0000000000 0x0018000008e00000

def z686 : W := mkw 0x6adf9e9a2812d7bc 0xeaac1ef08dfe32fd 0xfffffffff87807ff 0xfffc1fe00fff33ff

def z687 : W := mkw 0x1401404784cc3061 0x1153e10ff000a926 0x0000003e07fff800 0x0f03e01ff000fc07

def z688 : W := mkw 0x6adeda90a042c71c 0xc8be5ee00dfa12d8 0xfffffffff87807ff 0xf0ff5fe00fff33f8

def z689 : W := mkw 0x8f18e331c6678010 0x00ffeca5136b5400 0xfffffffffffff800 0x00ffe4633ffffc00

def z690 : W := mkw 0x0e00c20184440010 0x00ffec0500000000 0x0000000000000000 0x00fffc1f00000000

def z691 : W := mkw 0x3e8fd65facdcf3f9 0xbbfffffff8d6bbbf 0xf01fffffffffffff 0xfffffffff8ffffff

def z692 : W := mkw 0xdf38e335d767a452 0x04ffec07076bd542 0xfffffffffffff81f 0x00ffe4030ffffdc0

def z693 : W := mkw 0xd6ad143f3d11b6fa 0xaec19e178ec7f36f 0xfffffc3ffff807ff 0xffe39c1f0fe7f3ff

def z694 : W := mkw 0x000d041208109220 0x2200020080c2302c 0x001ffc0000780000 0xf000000000e03038

def z695 : W := mkw 0x0a00c20080400010 0x00be4da840000000 0x0000000000000000 0x00ff5ffcc0000000

def z696 : W := mkw 0x8d1de733ce779220 0x227fe308c3eb742c 0xfffffffffffff800 0xf0ffe380cffffc38

def z697 : W := mkw 0x6052088000024504 0x40000040053800d0 0xffe003c00000001f 0x00000000071801c0

def z698 : W := mkw 0xc6a010293501049a 0x8cc19c150e054241 0xffe0003fff800000 0x00e3981c0f07c000

def z699 : W := mkw 0x0085100220001228 0x880012008880222c 0x001ffc3e007807e0 0xff185b80c8e0323f

def z700 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe084030f07c3c7

def z701 : W := mkw 0xd620002515012452 0x04c18c070601c142 0xffe0003fff80001f 0x00e384030f07c1c0

def z702 : W := mkw 0x2002004000884101 0x1100004020100890 0x000003c00007f800 0x0004206030180c00

def z703 : W := mkw 0x28528a8000024104 0x402c00e001380090 0x000003c000000000 0x0004006000180000

def z704 : W := mkw 0x8d9cf739ee778288 0xaa7ff3184bef5609 0x0fe0fc01f8000000 0x00fb1b9c0fe70000

def z705 : W := mkw 0xc680102124010418 0x88c19c000e014240 0xffe0003fff8007ff 0x00e39c000f07c3c0

def z706 : W := mkw 0x2002000000004100 0x0000004000100090 0xf00003c00000001f 0x00040460001801c0

def z707 : W := mkw 0x68d69a802002470c 0xc82c12400db802d8 0xffffffc0000007ff 0xf0fc1b800ff803f8

def z708 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0xf01fffffffffffe0 0xff1ffffff8fffe3f

def z709 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff80001f 0x0fe39c1f0f07c1c7

def z710 : W := mkw 0x0f10e301c6660010 0x00ffedad51280400 0x000003c00007f800 0x00fffffff0180c00

def z711 : W := mkw 0x72c71cce289877fd 0xfb801ffaec94abff 0x00000000000007ff 0xff001ffff00003ff

def z712 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe7fc1f0f07c3c7

def z713 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffff03ffffffffff 0x0fe39c1f0f1fffc7

def z714 : W := mkw 0x6ad69a802002471c 0xc8ac1ee51db802d8 0xffffffc0000007ff 0xf0fc1fe33ff803f8

def z715 : W := mkw 0xd6a0102d350524da 0x8cc1bc171e05c343 0xffe0003fff8007ff 0x0fe3bc1f3f07c3c7

def z716 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0xffffffc007fff800 0x00fffffff7f8fc00

def z717 : W := mkw 0x291fe752cafed321 0x333e6348e1fa3cbc 0x001fffc0007ff800 0xf01c63e0f0f83c38

def z718 : W := mkw 0x8d18e331c6678000 0x007fe10d536b5400 0xfffffffffffff800 0x00ffe47ffffffc00

def z719 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fb9ffff0000000

def z720 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x00009ffff0000000

def z721 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffe060fffffc00

def z722 : W := mkw 0xbf12a36546af6151 0x11edace73339cd92 0xffe003c00787f81f 0x00e4a4633718cdc0

def z723 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0xf01ffffff87807e0 0xff1f5b9cc8ff323f

def z724 : W := mkw 0x0a00c20080440010 0x00be6dad50000000 0x0000000000000000 0x00181ffff0000000

def z725 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe79c7f0f07c3c7

def z726 : W := mkw 0x52a0100c310024da 0x8c801c170c048343 0xffe0003ff80007ff 0x0fe31c1f0f0703c7

def z727 : W := mkw 0xd4a0102d350124ca 0x8c4190120e05c343 0xffe0003fff8007ff 0x0fe3981c0f07c3c7

def z728 : W := mkw 0x0a10820000020010 0x00ac0dad51280000 0xffffffc000000000 0x00fc1ffffff80000

def z729 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fffbfff0000000

def z730 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0xf0000000000007ff 0x00fffffff00003c0

def z731 : W := mkw 0x2896920020024308 0x882c124009b80298 0xffffffc0000007ff 0xf0fc1fe00ff803f8

def z732 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe31c1f0f07c3c7

def z733 : W := mkw 0x0e08c21184448010 0x00ffedad50421000 0x001ffc0000780000 0x00fffffff0e03000

def z734 : W := mkw 0x87086131c6658010 0x00d3edad52435400 0x0000003ffffff800 0x0003fffff007fc00

def z735 : W := mkw 0x0a00c20080440010 0x00be6dad50000000 0x0000000000000000 0x001f7ffff0000000

def z736 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0f81f800ff803f8

def z737 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc1fe007f803f8

def z738 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc1fe3fff803f8

def z739 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fcfffff0000000

def z740 : W := mkw 0x4e00c20184440410 0x00ffedad54000040 0xffe000000000001f 0x00fffffff70001c0

def z741 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xfffffc3fff8007ff 0x0ffb9c1f0fe7c3c7

def z742 : W := mkw 0x8318213042238010 0x00800dad536b5400 0xfffffffffffff800 0x00001ffffffffc00

def z743 : W := mkw 0xd8a0d22cb14524ca 0x8c3e71ba5e05c343 0xffe0003fff8007ff 0x0f1c63e0ff07c3c7

def z744 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe00001ff8007ff 0x0fe39c1f0f07c3c7

def z745 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0x0ffffffffffff800 0x00ffe0000ffffc00

def z746 : W := mkw 0x64d65881a446470c 0xc853f34d5db802d8 0xffffffc0000007ff 0xf003e01ffff803f8

def z747 : W := mkw 0x9600002504012050 0x00c18c070201c102 0xffe0003fff8007ff 0x0fe39c1f0f07c3c7

def z748 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe39c1f0707c3c7

def z749 : W := mkw 0x0600400184440010 0x00d3edad50000000 0x0000000000000000 0x001bfffff0000000

def z750 : W := mkw 0x0c00c20184440000 0x007fe10840000000 0x0000000000000000 0x00fffffff0000000

def z751 : W := mkw 0x6a5bce9a8852d5b4 0x62be4df8c57e30f5 0xffe003fff878001f 0x0fe7447cc71f31c7

def z752 : W := mkw 0xd4a0102d350124ca 0x8c4190170e05c343 0xffe0003fff8007ff 0x0fe3801f0f07c3c7

def z753 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00fb40000ffffc00

def z754 : W := mkw 0x008d541aa85492a8 0xaa127318d8c6322d 0x001ffc3ff87807e0 0xff1b7b9cf8e7323f

def z755 : W := mkw 0xd7a0312d772524da 0x8cc1bc170e05c743 0xffe0003fff87ffff 0x0fe3bc1f0f07cfc7

def z756 : W := mkw 0x5ad59ac6208a367d 0xd9ac1ea2ada8ab6e 0x0fe0fc3e07fff800 0x0ff8fb83ffe0fc07

def z757 : W := mkw 0x4680100924000498 0x88c19c150c040241 0xffe0003ff80007ff 0x0fe39c1f0f0703c7

def z758 : W := mkw 0x6a568a8000024714 0x40ac0ee005b800d8 0xffffffc00000001f 0xf0fc1fe007f801f8

def z759 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffffffffffffffe0 0xf0ffe0000ffffe38

def z760 : W := mkw 0x0b18e310c2668010 0x00be6dad516a1400 0x001fffc0007ff800 0x001c7ffff0f83c00

def z761 : W := mkw 0x8d18e331c6678000 0x007fe108536b5400 0xfffffffffffff800 0x00ffe000fffffc00

def z762 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0ff1ffc0ff803f8

def z763 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc1b800ff803f8

def z764 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffffffc1fffff800 0x00ffe0000ffffc00

def z765 : W := mkw 0x8d95b72b6e3712a8 0xaa6db318cbad662d 0xffe003c00787ffe0 0xffe4bb9cc718ce3f

def z766 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x00181ffff0000000

def z767 : W := mkw 0x6ad69a802002471c 0xc8ac1ee50db802d8 0xffffffc0000007ff 0xf0fc1fff0ff803f8

def z768 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffe003fffffc00

def z769 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fcbfe33ff803f8

def z770 : W := mkw 0x0e00820104000010 0x00ed8ca500000000 0x0000000000000000 0x00fffffff0000000

def z771 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00ffbffff0000000

def z772 : W := mkw 0x8d18e331c6678000 0x007fe1a8536b5400 0xfffffffffffff800 0x00ffe3800ffffc00

def z773 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3fffffffe0 0xff1bfb9cc8e7fe3f

def z774 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x0004bffff0000000

def z775 : W := mkw 0x8d18a33146278000 0x006da000036b5400 0xfffffffffffff800 0x00fca0000ffffc00

def z776 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x0000fc01f80007e0 0xff1b5b9cc8e7023f

def z777 : W := mkw 0x008c5018a0408288 0x8812521008c61209 0x001ffc3ff87807e0 0xff1b5b9c08e7323f

def z778 : W := mkw 0x72a7144e399877fb 0xbf801f5fec94abff 0x00000000000007ff 0xff001ffff00003ff

def z779 : W := mkw 0x8d18a33146278000 0x006da000036b5400 0xfffffffffffff800 0x00e000000ffffc00

def z780 : W := mkw 0x0f08e311c6648010 0x00ffedad50421400 0x00000000007ff800 0x00fffffff0003c00

def z781 : W := mkw 0x0a00c20080440010 0x00be6dad50000000 0x0000000000000000 0x00fc7ffff0000000

def z782 : W := mkw 0x6286100020004718 0x88801e400c9002d8 0xffffffc0000007ff 0xf0fc1fe00ff803f8

def z783 : W := mkw 0xd6a0102d350124da 0x8cc19cb71e05c343 0xffe0003fff8007ff 0x0fe39c7f3f07c3c7

def z784 : W := mkw 0x8f00e321c6650010 0x00ffedad52014400 0x000000000787f800 0x00fffffff000cc00

def z785 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00fb80000ffffc00

def z786 : W := mkw 0x4e50ca8184460414 0x40ffedad55280040 0x0fe0000000000000 0x00fffffff7000000

def z787 : W := mkw 0xe6a3106b358955bb 0x9dc19c55ae156af5 0x0fff03c1f87ff800 0xf0e7787cff1f3c38

def z788 : W := mkw 0xf0f718ee318b77ef 0xdd001252afbdebff 0xffffffffffffffff 0xff0000000fffffff

def z789 : W := mkw 0xd62d44379d51b672 0x26d3cf0fc6c3f16e 0xfffffc0007f8001f 0xf0f8c783c7e0f1f8

def z790 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf00003fe07ffffff 0xff04e463f018ffff

def z791 : W := mkw 0x0085140a281012a8 0xaa001318c884222d 0x001ffc3ff80007e0 0xff1b1b9cc8e7023f

def z792 : W := mkw 0x0200000000000010 0x00800dad50000000 0xf01f03fe07fff800 0x0004fffff018fc00

def z793 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00fbe0000ffffc00

def z794 : W := mkw 0xd620002d150124d2 0x04c18c170605c143 0xffe0003fff80001f 0x0fe3841f0f07c1c7

def z795 : W := mkw 0x68d69a802002470c 0xc82c12e00db802d8 0xffffffc0000007ff 0xf0fc03e00ff803f8

def z796 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe39c7fff07c3c7

def z797 : W := mkw 0x0e00820104040010 0x00edadad50000000 0x0000000000000000 0x00e4fffff0000000

def z798 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe31c1c0f07c3c7

def z799 : W := mkw 0x291be352c2eed121 0x113e61e8f17a3cb4 0x001fffc0007ff800 0xf01c63e0f0f83c38

def z800 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff8780000 0xff1b5b9cc8e7303f

def z801 : W := mkw 0x8d18e331c6678000 0x007fe0a0036b5400 0xfffffffffffff800 0x00ffe3e00ffffc00

def z802 : W := mkw 0x8f10a32146270010 0x00edadad53294400 0xffe003c00787f800 0x00e4bffff718cc00

def z803 : W := mkw 0x0200400080400010 0x00924dad50000000 0x0000000000000000 0x00035ffff0000000

def z804 : W := mkw 0xe7ce79b1e665c71c 0xc8d3fee00ed356d8 0x0000003fffffffff 0xf003ffe00007fff8

def z805 : W := mkw 0x8918a33042238000 0x002c0000036b5400 0xfffffffffffff800 0x00f800000ffffc00

def z806 : W := mkw 0x8d18e331c6678000 0x007fe108436b5400 0xfffffffffffff800 0x00fffffffffffc00

def z807 : W := mkw 0x0600400184440010 0x00d3edad50000000 0x0000000000000000 0x0007fffff0000000

def z808 : W := mkw 0x00845008a0400288 0x8812531848840209 0x001ffc3ff80007e0 0xff1b5b9cc8e7023f

def z809 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffe000cffffc00

def z810 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffff03ffffffffff 0x0fe7fc7fff1fffc7

def z811 : W := mkw 0x95096177c6edb061 0x1153e10ff243fd26 0x0000003ffffff800 0x0f03e01ff007fc07

def z812 : W := mkw 0xb19f357e6abbf3e9 0xbb001252abffffbf 0xffffffffffffffff 0xff0000000fffffff

def z813 : W := mkw 0x8f08e331c6658010 0x00ffedad52435400 0x00000001f8000000 0x00fffffff0070000

def z814 : W := mkw 0x0208401080408010 0x00924dad50421000 0x001ffc3ff8780000 0x001b5ffff8e73000

def z815 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0007fffff 0xf0fc7fe00ff83ff8

def z816 : W := mkw 0x0009401280409020 0x00124108c0423024 0x001ffc3ff87807e0 0xff1b5b9cc8e7323f

def z817 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00ff1ffff0000000

def z818 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00fffb800ffffc00

def z819 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x00041ffff0000000

def z820 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0xf01ffc3ff87807ff 0xff1b5f9cc8e733ff

def z821 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00fce0000ffffc00

def z822 : W := mkw 0x285fce928856d324 0x623e63e8d1fa30bc 0x001fffc000780000 0xf01c63e0f0f83038

def z823 : W := mkw 0x0000400080400000 0x0012410840000000 0x0000000000000000 0x001b5ffff0000000

def z824 : W := mkw 0x008d141a281092a8 0xaa00121088c6322d 0x001ffc3ff87807e0 0xff1b1b9c08e7323f

def z825 : W := mkw 0x0e00820104040010 0x00edadad50000000 0x0000000000000000 0x00e7bffff0000000

def z826 : W := mkw 0x8518213146238000 0x00418000036b5400 0xfffffffffffff800 0x00e7e0000ffffc00

def z827 : W := mkw 0xd620002d150124d2 0x04c18c170605c143 0xffe0003fff8007ff 0x0fe3841f0707c3c7

def z828 : W := mkw 0x6ad69a882002479c 0xc8ac1ef00dbc02d9 0xfffffffff80007ff 0xfffc1fe00fff03ff

def z829 : W := mkw 0xce20c22195450412 0x04ffedad56014040 0x0fe0000000000000 0x00fffffff7000000

def z830 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1b5b9c08e7323f

def z831 : W := mkw 0x0c00c20184440000 0x007fe1ad50000000 0x0000000000000000 0x001ffbfff0000000

def z832 : W := mkw 0x308f145e2898f3e9 0xbb001252a8d6bbbf 0x001ffc3ff87807ff 0xff00000008e733ff

def z833 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0xf00003c00787f800 0x00fffffff018cc00

def z834 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe3fc1fff07c3c7

def z835 : W := mkw 0x8600002104010010 0x00c18dad52014000 0xffe0003fff800000 0x00e39fffff07c000

def z836 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fffffffff 0x0fe3fc1f0f07ffc7

def z837 : W := mkw 0xbd9ff77feefff3e9 0xbb7ff252abffffbf 0xffffffffffffffff 0xffffe0000fffffff

def z838 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe3981c0f07c3c7

def z839 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff1cffe3f018ffff

def z840 : W := mkw 0x295fef92ca76d324 0x623e63e8c1fa34bc 0x001fffc0007ff800 0xf01c63e0c0f83c38

def z841 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00fff81c0ffffc00

def z842 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc5fe0cff803f8

def z843 : W := mkw 0xfe728ae5158b6557 0x55ed8ce72739c9d2 0xffe003c00787f81f 0x00e4a4633718cdc0

def z844 : W := mkw 0x0a00c20080400010 0x00be4dad50000000 0x0000000000000000 0x00ff5ffff0000000

def z845 : W := mkw 0x8f10e321c6670010 0x00ffedad53294400 0x0fe0000000000000 0x00fffffff7000000

def z846 : W := mkw 0xbd1be377c6eff161 0x117fe042a37bfdb6 0x0fe0fc01f80007ff 0xfffb0463ffe703ff

def z847 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffff003fff8007ff 0xffe39c1f0f07c3ff

def z848 : W := mkw 0x9529653fdf75b0e2 0x2653e11fc247f527 0x0000003ffffff800 0x0f03e01fc007fc07

def z849 : W := mkw 0xd6a4102d350126da 0x8cc19e170e85c34b 0xfffffc3fff8007ff 0xffe39c1f0fe7c3ff

def z850 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xfffffffe07ffffff 0xf0fc1fe00ff8fff8

def z851 : W := mkw 0x2a12820000024110 0x00ac0ce001380090 0xffffffc0000007ff 0xf0fc1fe00ff803f8

def z852 : W := mkw 0x5280100c200024d8 0x88801c120c048343 0xffe0003fff8007ff 0x0fe39c1f0f07c3c7

def z853 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000003e000007e0 0x0ffffffff0000207

def z854 : W := mkw 0xd620002d150124d2 0x04c18c170605c143 0xffe0003fff80001f 0x0fe39c1f0707c1c7

def z855 : W := mkw 0x0e18c21184468010 0x00ffedad516a1000 0xfffffffff8780000 0x00ffffffffff3000

def z856 : W := mkw 0x0600000104000010 0x00c18dad50000000 0x0000000000000000 0x00e31ffff0000000

def z857 : W := mkw 0x0e8d961b2c1492b8 0xaaedbeb598c6322d 0x001ffc3ff87807e0 0xffe4a46338e7323f

def z858 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03c007ffffff 0xff04e463f018ffff

def z859 : W := mkw 0x8d18e331c6678000 0x007fe10d536b5400 0xfffffffffffff800 0x00ffe01c0ffffc00

def z860 : W := mkw 0x8e00c22184450010 0x00ffedad52014000 0xffe0000007800000 0x00fffffff700c000

def z861 : W := mkw 0x0600400184400010 0x00d3cdad50000000 0x0000000000000000 0x00fbdffff0000000

def z862 : W := mkw 0x8e00c22184450010 0x00ffedad52014000 0xffff03fffffff800 0x00ffffffff1ffc00

def z863 : W := mkw 0x4a94920020020618 0x88ac1e000da80248 0xffffffc0000007ff 0xf0fc1f800ff803f8

def z864 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x001f0000000007e0 0xf0fffffff0000238

def z865 : W := mkw 0xc6a010293501049a 0x8cc19c150e054241 0xffe0003ff80007ff 0x0fe31c1c0f0703c7

def z866 : W := mkw 0x8e10c22184470010 0x00ffedad53294000 0xffffffffff800000 0x00ffffffffffc000

def z867 : W := mkw 0x8d18e331c6678000 0x007fe005036b5400 0xfffffffffffff800 0x00ffe01f0ffffc00

def z868 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xffff03fe07ffffff 0xffe4e463ff18ffff

def z869 : W := mkw 0x0a00820000040010 0x00ac2dad50000000 0x0000000000000000 0x00043ffff0000000

def z870 : W := mkw 0x3087144e289873e9 0xbb001252a894abbf 0x00000000000007ff 0xff000000000003ff

def z871 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0xf01ffc3ffff807e0 0xff1bdb9cc8e7f23f

def z872 : W := mkw 0x6ad69a882002479c 0xc8ac1ef00dbc02d9 0xffffffc0000007ff 0xfffc1ffc0ff803ff

def z873 : W := mkw 0x0a00c20080440010 0x00be6dad50000000 0x0000000000000000 0x001cfffff0000000

def z874 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0x001ffffffffff800 0x00fffffff0fffc00

def z875 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe3981f0f07c3c7

def z876 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe003ffff87ffff 0x0fe7bc1f0f1fcfc7

def z877 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x0000fc01f80007e0 0xff1b1b9c08e7023f

def z878 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x0000fc3ff87807e0 0xff1b5b9cc8e7323f

def z879 : W := mkw 0x8f08e331c6658010 0x00ffedad52435400 0x001ffc3ffffff800 0x00fffffff8e7fc00

def z880 : W := mkw 0x000d441a885092a0 0x22124318c0c6302d 0x001ffc3ff8780000 0xff1b5b9cc0e7303f

def z881 : W := mkw 0x0600400184400010 0x00d3cd0d40000000 0x0000000000000000 0x00fffffff0000000

def z882 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0x0fe00001f80007ff 0x0fe3181c0f0703c7

def z883 : W := mkw 0x0600000104040010 0x00c1adad50000000 0x0000000000000000 0x0000bffff0000000

def z884 : W := mkw 0x428d5412a8509638 0xaa925f08ccc2326c 0xfffffc00007807ff 0xf0f85f80cfe033f8

def z885 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe00001f80007ff 0x0fe31c1f0f0703c7

def z886 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0ffb9f9f0f07c3c7

def z887 : W := mkw 0xd6a4102d350126da 0x8cc19e170e85c34b 0xffe0fc3fff8007ff 0x0ffb9f9f0fe7c3c7

def z888 : W := mkw 0x8918e330c2678000 0x003e6000036b5400 0xfffffffffffff800 0x00fc60000ffffc00

def z889 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffe4633ffffc00

def z890 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ff00000ffffc00

def z891 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ff60000ffffc00

def z892 : W := mkw 0x308e545ca8d8e3c9 0xbb12535a68d69b9b 0xf000ffc1ff87f81f 0x001fbfff38ffcdc0

def z893 : W := mkw 0x3e03c24784cc7171 0x11ffedeff010a9b6 0xf01f03fe07ffffff 0xfffb1b9c0018ffff

def z894 : W := mkw 0x9420002d150120c2 0x044180170205c103 0xffe0003fff8007ff 0x0fe3841f0f07c3c7

def z895 : W := mkw 0x0000000000000000 0x0000010840000000 0x0000000000000000 0x0004fffff0000000

def z896 : W := mkw 0xd6e418ad350126de 0xccc19eb70e85c34b 0xffe0003fff8007ff 0x0fe39f9f0f07c3c7

def z897 : W := mkw 0x70df1cde289af7ed 0xfb001252adfebbff 0xffffffffffffffff 0xff0000000fffffff

def z898 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x0000fc3ff80007e0 0xff1b1b9cc8e7023f

def z899 : W := mkw 0x4289541aa85094b8 0xaa925d18cc463265 0xffe0003ff87807ff 0x0fe35c1ccf0733c7

def z900 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc07e00ff803f8

def z901 : W := mkw 0x4a84920020000618 0x88ac1ea00c800248 0xfffffc00000007ff 0xf0fc1fe00fe003f8

def z902 : W := mkw 0x0800c20080440000 0x003e61a850000000 0x0000000000000000 0x001ffffff0000000

def z903 : W := mkw 0x62d618802002471c 0xc8801e400db802d8 0xffffffc0000007ff 0xf0f81f800ff803f8

def z904 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffe0fffffffff800 0x00ffe0000ffffc00

def z905 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000003e07fff800 0x00fffffff000fc00

def z906 : W := mkw 0xc680102924010498 0x88c19c100e054241 0xffe0003fff8007ff 0x0fe39c1c0f07c3c7

def z907 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xfffffffe078007ff 0xf0fc9fe00ff8c3f8

def z908 : W := mkw 0x0200400080400010 0x00924dad50000000 0x0000000000000000 0x00185ffff0000000

def z909 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x001f03c0007ff800 0x00fffffff0183c00

def z910 : W := mkw 0x6bd6bb806226471c 0xc8ac3ee00db806d8 0xffffffc00007ffff 0xf0fc3fe00ff80ff8

def z911 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffa0000ffffc00

def z912 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0x0fe0fc3ffffff800 0x00ffffffffe7fc00

def z913 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03fe07ffffff 0xff07fc7ff018ffff

def z914 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe7bc7f3f07c3c7

def z915 : W := mkw 0x008c5418a8508288 0xaa12531848c61209 0x001ffc3ff80007e0 0xff1b1b9c08e7023f

def z916 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffe4600ffffc00

def z917 : W := mkw 0x8d18a33146278000 0x006da000036b5400 0xfffffffffffff800 0x00e4e0000ffffc00

def z918 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0f81fe00ff803f8

def z919 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fcffe00ff803f8

def z920 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fbfffff0000000

def z921 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x0000fffff0000000

def z922 : W := mkw 0x8f10e321c6670010 0x00ffedad53294400 0xffe003ffff87f800 0x00ffffffff1fcc00

def z923 : W := mkw 0x6a568a8000024714 0x40ac0ee005b800d8 0xffffffc00000001f 0xf0fc07e00ff801f8

def z924 : W := mkw 0x72e718ce318877ff 0xdd801ef7ac94abff 0x00000000000007ff 0xff001ffff00003ff

def z925 : W := mkw 0x008d545aa8d892a9 0xbb125318e8c63a2d 0x001ffc3ff87fffe0 0xff1b7b9cf8e73e3f

def z926 : W := mkw 0x0a00820000000010 0x00ac0dad50000000 0x0000000000000000 0x00f81ffff0000000

def z927 : W := mkw 0x408d541aa85096a8 0xaa125318ccc6326d 0xfffffc3ff87807ff 0xff1b5b9ccfe733ff

def z928 : W := mkw 0x8918a33042238000 0x002c0000036b5400 0xfffffffffffff800 0x00fce0000ffffc00

def z929 : W := mkw 0x8d18a33146238000 0x006d8000036b5400 0xfffffffffffff800 0x00ff80000ffffc00

def z930 : W := mkw 0x0f18e311c6668010 0x00ffedad516a1400 0x0000fc0000000000 0x00fffffff0e00000

def z931 : W := mkw 0x0e00820104040010 0x00edadad50000000 0x0000000000000000 0x00fcbffff0000000

def z932 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0x0fe0fc00000007ff 0xf0f81b800fe003f8

def z933 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0xf01fffffffffffe0 0xff1b5b9cc8fffe3f

def z934 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffffffffffffffe0 0x0fffe0000ffffe07

def z935 : W := mkw 0x8d18e331c6678000 0x007fe1ad536b5400 0xfffffffffffff800 0x00ffe3fffffffc00

def z936 : W := mkw 0x018d751aea7492a8 0xaa127318c8c6362d 0x001ffc3ff87fffe0 0xff1b7b9cc8e73e3f

def z937 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc01f87807e0 0xff1b5b9cc8e7323f

def z938 : W := mkw 0x8d18e331c6678000 0x007fe108436b5400 0xfffffffffffff800 0x00ffe380cffffc00

def z939 : W := mkw 0x0200400080400010 0x00924dad50000000 0x0000000000000000 0x001b1ffff0000000

def z940 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0x0fffffc1f87ff800 0x00ffffffffff3c00

def z941 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0x0ffffc3ff8780000 0x00ffffffffe73000

def z942 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0x0fe0003fff8007ff 0x0fe39c1f0f07c3c7

def z943 : W := mkw 0x94a4102d350122ca 0x8c4192170a85c30b 0x001ffc3fff8007e0 0xff1b9b9f08e7c23f

def z944 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0x0fe0fc01f8000000 0x00fb1fffffe70000

def z945 : W := mkw 0x0600000104000010 0x00c18dad50000000 0x0000000000000000 0x00039ffff0000000

def z946 : W := mkw 0x8d18e331c6678000 0x007fe0a0136b5400 0xfffffffffffff800 0x00ffe0603ffffc00

def z947 : W := mkw 0x5bb8f31cf366a4da 0x8cbe7c170d6e9743 0x001fffc0007fffff 0x0f1c7c1f00f83fc7

def z948 : W := mkw 0xf0af147e3999f7eb 0xbf001252aed7fbff 0xffffffffffffffff 0xff0000000fffffff

def z949 : W := mkw 0x8408403184418000 0x0053c00002435000 0xfffffffffffff800 0x00ffe0000ffffc00

def z950 : W := mkw 0x8d18e331c6678000 0x007fe10d536b5400 0xfffffffffffff800 0x00fffb9ffffffc00

def z951 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00fb5ffff0000000

def z952 : W := mkw 0x6ad69a802006471c 0xc8ac3ee01db802d8 0xffffffc0000007ff 0xf0fc3fe03ff803f8

def z953 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x00005ffff0000000

def z954 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1ffb9cc8e7323f

def z955 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00e7fffff0000000

def z956 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00ffe4030ffffc00

def z957 : W := mkw 0x8e08c23184458010 0x00ffedad52435000 0xfffffc3ffff80000 0x00ffffffffe7f000

def z958 : W := mkw 0xd6a0106d358924db 0x9dc19c172e05cb43 0xffe0003fff87ffff 0x0fe3bc1f3f07cfc7

def z959 : W := mkw 0x285fced288dad325 0x733e43e8e1fa38bc 0x001fffc0007ff800 0xf01c63e0f0f83c38

def z960 : W := mkw 0x8d18e331c6678000 0x007fe1a8536b5400 0xfffffffffffff800 0x00fffbfcfffffc00

def z961 : W := mkw 0xbc768aad150363c6 0x446d82f703bdc19b 0x001fffffff800000 0xff1f83ff00ffc03f

def z962 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffff003ffff807ff 0x0fe3dc1f0f07f3c7

def z963 : W := mkw 0x0008401080408000 0x0012410840421000 0xf01ffffffffff800 0x001ffffff8fffc00

def z964 : W := mkw 0x0f18e311c6668010 0x00ffedad516a1400 0x001ffffff87ff800 0x00fffffff8ff3c00

def z965 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1f5ffcc8e7323f

def z966 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffe0fc00000007ff 0xf0f81fe00fe003f8

def z967 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc01f80007e0 0xff1b1b9cc8e7023f

def z968 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc9fe30ff803f8

def z969 : W := mkw 0x0a00820000000010 0x00ac0dad50000000 0x0000000000000000 0x00e41ffff0000000

def z970 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xfffffffe07ffffff 0xf0fcffe3fff8fff8

def z971 : W := mkw 0x6ad69a882002479c 0xc8ac1ef00dbc02d9 0xffffffc1f80007ff 0xf0ff1ffc0fff03f8

def z972 : W := mkw 0x8d18e331c6678000 0x007fe108436b5400 0xfffffffffffff800 0x00ffe01ccffffc00

def z973 : W := mkw 0x8d18a33146278000 0x006da000036b5400 0xfffffffffffff800 0x00e7a0000ffffc00

def z974 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0xffe0000000000000 0x00ffffffff000000

def z975 : W := mkw 0x9480102d240120c8 0x884190120a05c303 0xffe0003fff8007ff 0x0fe39c1f0f07c3c7

def z976 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0xfffffc3ff87807e0 0xfffb5b9ccfe7323f

def z977 : W := mkw 0x8f08e331c6658010 0x00ffedad52435400 0xf01f03fffffff800 0x00fffffff01ffc00

def z978 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1bdf9fc8e7323f

def z979 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe3dc1fcf07c3c7

def z980 : W := mkw 0x8d18e331c6678000 0x007fe108436b5400 0xfffffffffffff800 0x00fffb9c0ffffc00

def z981 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000003ff8000000 0x00fffffff8070000

def z982 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x00031ffff0000000

def z983 : W := mkw 0x9429447f9dd9b0e3 0x3753c11fe247f927 0x0000003ffffff800 0x0f03e01ff007fc07

def z984 : W := mkw 0x0600000104000010 0x00c18dad50000000 0x0000000000000000 0x00e09ffff0000000

def z985 : W := mkw 0xd6a4102d350126da 0x8cc19e170e85c34b 0xffe0003fff8007ff 0xffe39f9f0f07c3ff

def z986 : W := mkw 0x308f545ea8d8f3e9 0xbb125252a8d6bbbf 0xf01fffffffffffff 0xff1fe00008ffffff

def z987 : W := mkw 0x8d18e331c6678000 0x007fe005136b5400 0xfffffffffffff800 0x00ffe0033ffffc00

def z988 : W := mkw 0xd2a0102c310124da 0x8c801c120e05c343 0xffe0003fff8007ff 0x0fe31c1c0f07c3c7

def z989 : W := mkw 0x0600000104000010 0x00c18dad50000000 0x0000000000000000 0x00e7fffff0000000

def z990 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0x0ffffc00000007ff 0xf0f81fe00fe003f8

def z991 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x00ff7ffff0000000

def z992 : W := mkw 0x0e10c20184460010 0x00ffedad51280000 0xffe003c000000000 0x00fffffff7180000

def z993 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0xffffffc1f8000000 0x00ffffffffff0000

def z994 : W := mkw 0x8c10822104030000 0x006d800003294000 0xfffffffffffff800 0x00ffe0000ffffc00

def z995 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01f03ffffffffff 0xff07e463f81fffff

def z996 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc00787ffff 0xf0fcbfe00ff8cff8

def z997 : W := mkw 0xd6a0102d350124da 0x8cc19cb70e05c343 0xffe0003fff8007ff 0x0fe39fff0f07c3c7

def z998 : W := mkw 0x8918e330c2638000 0x003e4000036b5400 0xfffffffffffff800 0x00ff40000ffffc00

def z999 : W := mkw 0x9509657fcefdb0e1 0x3353e11ae247fd27 0x0000003ffffff800 0x0f03e01ff007fc07

def z1000 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1b5ffff8e7323f

def z1001 : W := mkw 0x8e00c22184450010 0x00ffedad52014000 0x0000003fff800000 0x00fffffff007c000

def z1002 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1b5b9cc0e7323f

def z1003 : W := mkw 0x62c618802000471c 0xc8801ee00c9002d8 0xfffffc00000007ff 0xf0f81fe00fe003f8

def z1004 : W := mkw 0x0f18e311c6668010 0x00ffedad516a1400 0xffffffc0007ff800 0x00fffffffff83c00

def z1005 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0xf000003e07800000 0x00fffffff000c000

def z1006 : W := mkw 0x85186131c6638000 0x0053c000036b5400 0xfffffffffffff800 0x00fbc0000ffffc00

def z1007 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xfffffffffffff800 0x00e7e0000ffffc00

def z1008 : W := mkw 0x0600400184440010 0x00d3edad50000000 0x0000000000000000 0x00e3fffff0000000

def z1009 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffff03ffff8007ff 0x0fe79c1f0f1fc3c7

def z1010 : W := mkw 0x6af69a883102479e 0xccac1ef50dbc02d9 0xffffffc0000007ff 0xf0fc1ffc0ff803f8

def z1011 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0xf01f03c000000000 0x00fffffff0180000

def z1012 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0xffe003fffffff800 0x00fffffff71ffc00

def z1013 : W := mkw 0x0e08c21184448010 0x00ffedad50421000 0x0000fc01f8000000 0x00fffffff8e70000

def z1014 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0xf01ffffe07ffffff 0xff1ce463f8f8ffff

def z1015 : W := mkw 0x0000000000000000 0x0000010840000000 0x0000000000000000 0x00001ffff0000000

def z1016 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffe0ffc0000007ff 0xf0fc1fe00ff803f8

def z1017 : W := mkw 0x28d69a882002438c 0xc82c12f009bc0299 0x001ffffff80007e0 0xff1f1bfc08ff023f

def z1018 : W := mkw 0x8918a33042238000 0x002c0000036b5400 0xfffffffffffff800 0x00e400000ffffc00

def z1019 : W := mkw 0x8f08e331c6658010 0x00ffedad52435400 0xffe0003ffffff800 0x00ffffffff07fc00

def z1020 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x00e01ffff0000000

def z1021 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0xffe0ffc1ff87f800 0x00ffffffffffcc00

def z1022 : W := mkw 0x8f18e331c6678010 0x00ffedad536b5400 0xffe0fc3fff800000 0x00ffffffffe7c000

def z1023 : W := mkw 0x0a00820000000010 0x00ac0dad50000000 0x0000000000000000 0x00fcfffff0000000

def z1024 : W := mkw 0x8518213146238000 0x00418000036b5400 0xfffffffffffff800 0x00e080000ffffc00

def z1025 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc00000001f 0xf0fc1fe00ff801f8

def z1026 : W := mkw 0x8f10e321c6670010 0x00ffedad53294400 0xffffffc00787f800 0x00fffffffff8cc00

def z1027 : W := mkw 0xff72aba557276556 0x44edace70739c5d2 0xffe003c00787f81f 0x00e4a4630718cdc0

def z1028 : W := mkw 0x8d18e331c6678000 0x007fe1a8536b5400 0xfffffffffffff800 0x00ffe7e3fffffc00

def z1029 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc1be00ff803f8

def z1030 : W := mkw 0x0e10c20184460010 0x00ffedad51280000 0x0fe0fc0000000000 0x00ffffffffe00000

def z1031 : W := mkw 0x4ad49a802002061c 0xc8ac1ea00da80248 0xfffffc00000007ff 0xf0f81f800fe003f8

def z1032 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0x0fe0003ff80007ff 0x0fe31c1f0f0703c7

def z1033 : W := mkw 0x0f18e311c6668010 0x00ffedad516a1400 0xf01ffffe07fff800 0x00fffffff0f8fc00

def z1034 : W := mkw 0x3087144e289873e9 0xbb001252a894abbf 0xf01f03fe07ffffff 0xff0000000018ffff

def z1035 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0x0fffffc0000007ff 0xf0fc1fe00ff803f8

def z1036 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xfffffffe000007ff 0xfffc1fe00ff803ff

def z1037 : W := mkw 0xfe728aa515076556 0x44edace71739c1d2 0xffe003c00780001f 0x00e4a4633718c1c0

def z1038 : W := mkw 0x3003004600887161 0x11000042a010a9b6 0x001f03fe07ffffff 0xff04e463f018ffff

def z1039 : W := mkw 0x85186131c6678000 0x0053e000036b5400 0xfffffffffffff800 0x00e3e0000ffffc00

def z1040 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x001ffc0000000000 0x00fffffff8e00000

def z1041 : W := mkw 0x0200000000000010 0x00800dad50000000 0x0000000000000000 0x00047ffff0000000

def z1042 : W := mkw 0x0e00820104000010 0x00ed8dad50000000 0x0000000000000000 0x00ff9ffff0000000

def z1043 : W := mkw 0x8118213042238000 0x00000000036b5400 0xfffffffffffff800 0x00e000000ffffc00

def z1044 : W := mkw 0x8518213146238000 0x00418000036b5400 0xfffffffffffff800 0x00e300000ffffc00

def z1045 : W := mkw 0x0e08c21184448010 0x00ffedad50421000 0x0000003ff8780000 0x00fffffff0073000

def z1046 : W := mkw 0x8d18e331c6678000 0x007fe000036b5400 0xffffffffffffffff 0x00ffe4000fffffc0

def z1047 : W := mkw 0x0200400080440010 0x00926dad50000000 0x0000000000000000 0x00007ffff0000000

def z1048 : W := mkw 0x0e08c21184448010 0x00ffedad50421000 0xf01ffffffffff800 0x00fffffff8fffc00

def z1049 : W := mkw 0x8f10e321c6670010 0x00ffedad53294400 0xffff03fe07fff800 0x00fffffff718fc00

def z1050 : W := mkw 0x0818c21080428000 0x003e4000016a1000 0xfffffffffffff800 0x00ffe0000ffffc00

def z1051 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1f7bfcf8e7323f

def z1052 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1b1b9cc8e7323f

def z1053 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffffff87fffe0 0xff1f7b9cc8ff3e3f

def z1054 : W := mkw 0x0e10c20184460010 0x00ffedad51280000 0x001fffc000000000 0x00fffffff0f80000

def z1055 : W := mkw 0x8e00c22184450010 0x00ffedad52014000 0x0fe00001f8000000 0x00ffffffff070000

def z1056 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0xffe0003fff8007ff 0x0fe3841f0f07c3c7

def z1057 : W := mkw 0x0085100a200012a8 0x880012108884222d 0x001ffc3ff87807e0 0xff1b5b9cc8e7323f

def z1058 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xffffffc0000007ff 0xf0fc7fe0fff803f8

def z1059 : W := mkw 0x6ad69ac0208a471d 0xd9ac1ee02db80ad8 0xffffffc00007ffff 0xf0fc3fe03ff80ff8

def z1060 : W := mkw 0x6a568a8000024714 0x40ac0ee005b800d8 0xffffffc0000007ff 0xf0fc07e007f803f8

def z1061 : W := mkw 0x0e00820104040010 0x00edadad50000000 0x0000000000000000 0x00e01ffff0000000

def z1062 : W := mkw 0x008d541aa85092a8 0xaa125318c8c6322d 0x001ffc3ff87807e0 0xff1bfb9ff8e7323f

def z1063 : W := mkw 0x0200400080400010 0x00924dad50000000 0x0000000000000000 0x001ffffff0000000

def z1064 : W := mkw 0x0e10c20184460010 0x00ffedad51280000 0xfffffffe07fff800 0x00fffffffff8fc00

def z1065 : W := mkw 0x0400400184440000 0x0053e10d50000000 0x0000000000000000 0x001ffffff0000000

def z1066 : W := mkw 0x0a00c20080400010 0x00be4da840000000 0x0000000000000000 0x00fffffff0000000

def z1067 : W := mkw 0x0600400184440010 0x00d3edad50000000 0x0000000000000000 0x00031ffff0000000

def z1068 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0x0fe0fc00000007ff 0xf0fc1fe00fe003f8

def z1069 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x0000000000000000 0x001ffffff0000000

def z1070 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xfffffffff80007ff 0xf0ff1fe00fff03f8

def z1071 : W := mkw 0x0e00c20184440010 0x00ffedad50000000 0x001f003e00780000 0x00fffffff0003000

def z1072 : W := mkw 0xd6a0102d350124da 0x8cc19c170e05c343 0x0fe00001f80007ff 0x0fe39c1f0f0703c7

def z1073 : W := mkw 0x9429443f9d55b0e2 0x2653e11fd247f127 0x0000003ffff80000 0x0f03e01ff007f007

def z1074 : W := mkw 0x6ad69a802002471c 0xc8ac1ee00db802d8 0xfffffffe007807ff 0xf0fc5fe00ff833f8

def z1075 : W := mkw 0x28568a8000024304 0x402c02e001b80098 0xffffffc0000007ff 0xf0fc07e00ff803f8

def z1076 : W := mkw 0x0a00820000000010 0x00ac0dad50000000 0x0000000000000000 0x001c1ffff0000000

def z1077 : W := mkw 0x4284100820000698 0x88801e100c840249 0xfffffc3ff80007ff 0xfffb1f9c0fe703ff

def z1078 : W := mkw 0x8f95b72b6e3712b8 0xaaedbeb59bad662d 0xffe003c00787ffe0 0xffe4a4633718ce3f

def z1079 : W := mkw 0x59b8f31cf366a4ca 0x8c3e71ba5d6e9743 0x001fffc0007fffff 0x0f1c63e0f0f83fc7

def z1080 : W := mkw 0x4200000800000490 0x00800c1004040041 0xffe0003ff800001f 0x0fe3041c070701c7

def z1081 : W := mkw 0x8d18e331c6678000 0x007fe1ad536b5400 0xfffffffffffff800 0x00fffbfffffffc00

def z1082 : W := mkw 0x8d18e331c6678000 0x007fe1a8536b5400 0xfffffffffffff800 0x00fffffffffffc00

def z1083 : W := mkw 0x8d18e331c6678000 0x007fe10d536b5400 0xfffffffffffff800 0x00fffffffffffc00

def z1084 : W := mkw 0xe5ce79b1e665c70c 0xc853f34d5ed356d8 0x0000003fffffffff 0xf003e01ff007fff8

def z1085 : W := mkw 0x4204000000000610 0x00800e0004800048 0xfffffc000000001f 0xf0f8078007e001f8

def z1086 : W := mkw 0xd4a0102d350124ca 0x8c4191ba5e05c343 0xffe0003fff8007ff 0x0fe383e0ff07c3c7

def z1087 : W := mkw 0x68d69a802002470c 0xc82c134d5db802d8 0xffffffc0000007ff 0xf0fc001ffff803f8

def z1088 : W := mkw 0x028d541aa85092b8 0xaa925eb598c6322d 0x001ffc3ff87807e0 0xff1b446338e7323f

def bk0_0 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z0,z1,z2,z3,z7,z6])],[(0,[z8,z0,z9,z2,z3,z4,z6]),(0,[z10,z0,z1,z11,z3,z4,z6]),(0,[z0,z12,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z13,z3,z4,z6]),(0,[z0,z1,z2,z3,z14,z4,z6])],[(0,[z15,z1,z2,z16,z3,z4,z6]),(1,[z0,z17,z2,z3,z4,z6])],[(0,[z0,z1,z18,z2,z19,z4,z6]),(0,[z0,z1,z2,z3,z4,z20,z6]),(0,[z0,z1,z21,z3,z19,z4,z6]),(0,[z1,z2,z3,z22,z4,z23,z6])],[],[(0,[z24,z0,z1,z2,z3,z4,z25]),(0,[z0,z26,z1,z2,z3,z4,z6])],[(0,[z27,z0,z1,z2,z3,z4,z6]),(0,[z0,z28,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z29,z3,z5,z6])],[(0,[z0,z1,z2,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z31,z6])],[(0,[z0,z32,z1,z2,z3,z33,z6])],[(0,[z0,z1,z34,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z35,z4,z6])],[(0,[z36,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z37,z4,z6]),(0,[z0,z1,z2,z3,z38,z4,z6]),(0,[z0,z1,z2,z3,z4,z39,z6])],[(0,[z40,z41,z1,z2,z3,z4,z6]),(0,[z0,z42,z1,z2,z3,z4,z6])],[(0,[z0,z43,z1,z2,z29,z3,z4]),(0,[z0,z1,z11,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z44,z4,z6]),(1,[z0,z1,z2,z3,z4,z45])],[(0,[z40,z0,z2,z46,z3,z4,z6]),(0,[z47,z0,z1,z2,z3,z4,z6])],[(0,[z0,z48,z1,z2,z3,z4,z6]),(0,[z0,z49,z1,z2,z3,z4,z6]),(1,[z24,z1,z2,z3,z4,z50])],[]]

def bk0_1 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z51,z2,z3,z4,z6]),(0,[z0,z1,z52,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z53,z6]),(1,[z0,z1,z2,z3,z4,z54])],[(0,[z0,z55,z1,z2,z3,z56,z6]),(0,[z0,z57,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z58])],[(0,[z0,z59,z2,z3,z4,z5,z6]),(1,[z0,z2,z60,z3,z5,z6])],[(0,[z0,z9,z2,z3,z61,z4,z6])],[(0,[z62,z0,z1,z63,z3,z4,z6]),(0,[z64,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z65,z3,z4,z6]),(0,[z0,z1,z2,z3,z66,z22,z6]),(0,[z0,z1,z2,z3,z67,z4,z6])],[],[(0,[z0,z68,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z69,z70])],[(0,[z0,z71,z1,z2,z3,z4,z6]),(1,[z72,z1,z2,z3,z4,z6])],[],[],[],[(0,[z73,z0,z1,z2,z3,z4,z6]),(0,[z0,z74,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z75,z6])],[(0,[z0,z76,z1,z2,z3,z4,z6]),(0,[z0,z32,z1,z2,z61,z4,z6]),(0,[z0,z1,z2,z77,z3,z4,z6]),(1,[z0,z78,z2,z3,z4,z6])],[(0,[z0,z1,z2,z79,z3,z4,z6]),(0,[z0,z1,z2,z79,z3,z4,z80]),(0,[z0,z1,z2,z3,z81,z4,z6]),(0,[z0,z1,z2,z3,z4,z82,z6]),(0,[z0,z83,z2,z46,z3,z4,z6])],[(0,[z40,z0,z1,z2,z3,z84,z6]),(0,[z0,z85,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z86,z6])]]

def bk0_2 : List (List (ℕ × List W)) :=
  [[(0,[z87,z1,z2,z3,z4,z23,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z3,z4,z6,z80])],[(0,[z88,z0,z1,z2,z3,z23,z6]),(0,[z0,z89,z2,z3,z61,z4,z6]),(0,[z0,z1,z90,z2,z3,z4,z6])],[(0,[z72,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z91,z6]),(0,[z0,z1,z2,z3,z4,z6,z92])],[(0,[z0,z1,z93,z2,z3,z4,z6]),(0,[z0,z1,z2,z94,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z95])],[(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z97,z2,z3,z4,z6]),(0,[z0,z1,z98,z2,z3,z4,z6])],[(0,[z0,z1,z99,z2,z3,z4,z6])],[(0,[z100,z0,z1,z2,z3,z4,z6]),(0,[z101,z1,z2,z102,z3,z4,z6]),(0,[z0,z1,z103,z2,z3,z4,z6])],[(0,[z104,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z61,z4,z6])],[(0,[z0,z105,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z106,z3,z4,z6]),(0,[z0,z1,z2,z3,z107,z4,z6]),(0,[z0,z1,z2,z3,z4,z108,z6])],[(0,[z36,z109,z1,z2,z3,z4,z6]),(0,[z0,z9,z85,z2,z3,z4,z6]),(0,[z0,z1,z2,z60,z3,z5,z6]),(0,[z0,z1,z2,z110,z3,z4,z6]),(0,[z0,z1,z2,z3,z111,z4,z6]),(0,[z0,z2,z3,z4,z5,z112,z6])],[(0,[z0,z1,z2,z3,z4,z113,z6])],[(0,[z0,z9,z2,z46,z3,z4,z6])],[(0,[z36,z1,z114,z2,z3,z4,z6]),(0,[z0,z115,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z116,z6,z69]),(1,[z0,z32,z2,z117,z4,z6])],[(0,[z118,z0,z1,z2,z3,z4,z6])],[(0,[z0,z9,z55,z2,z3,z4,z6])],[(0,[z40,z0,z1,z2,z3,z91,z6]),(0,[z24,z0,z9,z2,z3,z4,z6]),(0,[z1,z2,z102,z3,z38,z4,z6])]]

def bk0_3 : List (List (ℕ × List W)) :=
  [[],[],[(0,[z119,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z120,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z121])],[(0,[z122,z0,z1,z2,z3,z4,z6]),(0,[z123,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z78,z2,z3,z4,z6])],[(0,[z0,z9,z42,z2,z3,z4,z6]),(0,[z0,z124,z1,z2,z3,z125,z6])],[(0,[z0,z1,z2,z117,z19,z4,z6])],[(0,[z0,z1,z126,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z127,z4,z6])],[(0,[z128,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z129,z6])],[(1,[z0,z130,z2,z3,z4,z6])],[(0,[z0,z9,z131,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z132,z6]),(0,[z0,z1,z2,z3,z4,z6,z133])],[(0,[z62,z0,z1,z2,z134,z4,z6]),(1,[z0,z135,z2,z3,z4,z6])],[(0,[z0,z1,z136,z2,z3,z4,z6]),(0,[z0,z1,z2,z137,z3,z4,z6])],[(0,[z0,z1,z2,z138,z3,z4,z6]),(0,[z0,z1,z2,z3,z139,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z54]),(0,[z0,z2,z117,z3,z4,z5,z6])],[(0,[z0,z9,z9,z2,z3,z4,z6]),(0,[z0,z1,z59,z2,z102,z4,z6]),(0,[z0,z1,z2,z140,z3,z4,z6]),(0,[z0,z1,z2,z3,z141,z4,z6]),(0,[z0,z1,z2,z3,z125,z4,z6]),(1,[z0,z1,z2,z3,z4,z142])],[(0,[z0,z2,z3,z4,z5,z5,z6])]]

def bk0_4 : List (List (ℕ × List W)) :=
  [[(0,[z143,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z144,z4,z6])],[(0,[z0,z1,z145,z2,z3,z4,z6])],[(0,[z146,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z147])],[],[(0,[z0,z148,z1,z2,z3,z5,z6]),(0,[z0,z149,z1,z2,z3,z4,z6])],[(0,[z150,z0,z1,z2,z3,z4,z6]),(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z151,z2,z3,z4,z6])],[(0,[z152,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z18,z2,z3,z4,z6]),(0,[z0,z1,z2,z153,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z45,z6])],[(0,[z0,z9,z2,z3,z4,z6,z70]),(0,[z0,z154,z1,z2,z3,z4,z155]),(0,[z0,z1,z2,z3,z66,z156,z6])],[(0,[z0,z17,z2,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z157,z4,z6])],[],[(0,[z87,z0,z1,z2,z3,z4,z6])],[(0,[z158,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z159,z70])],[(0,[z0,z1,z160,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z66,z116,z6])],[(0,[z0,z89,z1,z2,z117,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z161])],[(0,[z0,z1,z2,z3,z4,z162,z6]),(0,[z0,z1,z2,z3,z4,z50,z80])]]

def bk0_5 : List (List (ℕ × List W)) :=
  [[],[],[(0,[z163,z0,z1,z2,z3,z4,z6])],[(0,[z164,z0,z1,z2,z3,z4,z6]),(0,[z0,z154,z124,z2,z3,z4,z6]),(0,[z0,z1,z2,z16,z3,z4,z6]),(0,[z0,z1,z2,z3,z165,z4,z6]),(0,[z0,z1,z2,z3,z4,z166,z6]),(0,[z0,z1,z2,z19,z4,z6,z167])],[(0,[z0,z1,z168,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z169,z4,z6]),(0,[z0,z1,z2,z3,z170,z4,z6])],[(0,[z15,z10,z1,z2,z3,z4,z6]),(0,[z0,z1,z171,z2,z3,z4,z6]),(0,[z0,z1,z2,z172,z3,z4,z6])],[(0,[z0,z173,z1,z2,z3,z4,z6]),(0,[z0,z174,z1,z46,z3,z4,z6]),(1,[z175,z1,z2,z3,z4,z6])],[],[(0,[z24,z0,z2,z3,z4,z5,z6]),(0,[z0,z176,z1,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z6,z177]),(0,[z0,z2,z3,z56,z4,z178,z6])],[(0,[z0,z179,z1,z2,z3,z4,z6]),(0,[z0,z1,z59,z2,z3,z4,z6]),(0,[z0,z1,z59,z2,z3,z4,z80]),(0,[z0,z1,z63,z2,z3,z4,z6])],[(0,[z88,z0,z9,z2,z3,z4,z6]),(0,[z0,z180,z1,z2,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z4,z69])],[(0,[z0,z154,z2,z3,z4,z6,z155]),(0,[z0,z2,z3,z4,z181,z5,z6])],[(0,[z182,z0,z1,z2,z3,z4,z6]),(0,[z183,z0,z1,z2,z3,z4,z6]),(0,[z184,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z185,z2,z3,z4,z6]),(0,[z0,z32,z89,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z186]),(1,[z0,z55,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z4,z187])],[(0,[z0,z154,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z80])]]

def bk0_6 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z188,z4,z5,z6])],[(0,[z189,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z190,z3,z4,z6])],[(0,[z88,z0,z1,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z6,z191]),(0,[z0,z2,z3,z4,z192,z5,z6])],[(0,[z40,z0,z9,z2,z3,z4,z6])],[],[(0,[z193,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z6,z155])],[(0,[z0,z1,z185,z2,z3,z4,z75]),(0,[z0,z1,z131,z18,z3,z4,z6]),(0,[z0,z1,z194,z2,z3,z4,z6]),(0,[z0,z1,z195,z2,z3,z4,z6])],[(0,[z36,z0,z114,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z5,z6]),(0,[z0,z76,z2,z3,z169,z4,z6]),(0,[z0,z196,z1,z2,z3,z4,z6]),(0,[z0,z114,z2,z3,z4,z5,z6])],[(0,[z197,z0,z1,z2,z3,z4,z6]),(0,[z0,z135,z2,z3,z116,z4,z6]),(0,[z0,z1,z198,z2,z3,z4,z6]),(0,[z0,z1,z199,z2,z3,z4,z6])],[(0,[z0,z2,z102,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z113,z6])],[(0,[z0,z1,z2,z200,z3,z4,z6]),(1,[z0,z2,z201,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z202]),(0,[z1,z2,z16,z3,z4,z23,z6])],[(0,[z0,z85,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z203])],[(0,[z8,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z6,z204])],[(0,[z0,z205,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z206,z6]),(0,[z0,z1,z2,z3,z4,z6,z207]),(1,[z0,z9,z2,z3,z5,z6])],[(0,[z0,z2,z3,z22,z4,z5,z6])]]

def bk0_7 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z3,z4,z208,z6])],[(0,[z0,z1,z2,z209,z3,z4,z6])],[(0,[z8,z0,z1,z2,z79,z3,z4])],[(0,[z0,z1,z2,z3,z22,z4,z6])],[],[(0,[z0,z210,z1,z2,z3,z4,z6]),(0,[z0,z89,z2,z3,z4,z5,z6])],[(0,[z0,z1,z2,z3,z4,z211,z6]),(0,[z0,z1,z2,z3,z4,z212,z6])],[(0,[z0,z9,z83,z2,z3,z4,z6]),(0,[z0,z1,z2,z213,z3,z4,z6])],[(0,[z118,z0,z1,z2,z3,z4,z142]),(0,[z118,z1,z2,z3,z4,z25,z6]),(0,[z0,z1,z63,z2,z3,z169,z6]),(0,[z0,z1,z2,z214,z3,z4,z6]),(0,[z0,z2,z77,z3,z4,z5,z6])],[(0,[z0,z9,z2,z117,z3,z4,z6]),(0,[z0,z1,z2,z3,z116,z4,z6])],[(0,[z0,z1,z2,z3,z215,z4,z6])],[(0,[z0,z1,z185,z3,z4,z6,z70]),(0,[z0,z1,z216,z3,z4,z75,z6]),(0,[z0,z63,z2,z3,z4,z5,z6])],[(0,[z217,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z218,z6])],[(0,[z0,z219,z1,z2,z3,z4,z6])],[(0,[z8,z0,z1,z59,z2,z3,z4])],[(0,[z0,z1,z220,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z69])]]

def bk0_8 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z195,z2,z3,z38,z4]),(0,[z0,z1,z2,z221,z3,z4,z6]),(0,[z0,z1,z2,z222,z3,z4,z6]),(0,[z0,z1,z2,z223,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z224]),(0,[z0,z1,z2,z3,z4,z6,z225])],[(0,[z0,z1,z226,z2,z3,z4,z6]),(0,[z0,z1,z2,z201,z3,z4,z6])],[(0,[z0,z9,z2,z3,z4,z23,z6])],[(0,[z227,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z228])],[(0,[z0,z1,z2,z229,z3,z4,z6]),(0,[z0,z1,z2,z102,z4,z6,z80]),(0,[z0,z1,z2,z3,z4,z230,z6])],[(0,[z0,z231,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z232,z3,z4,z6])],[(0,[z0,z9,z2,z3,z4,z6,z80]),(0,[z0,z233,z1,z2,z3,z4,z6]),(0,[z0,z124,z1,z2,z3,z4,z159])],[(0,[z234,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z235,z2,z3,z4,z6]),(0,[z0,z1,z2,z79,z3,z4,z112])],[(0,[z236,z0,z1,z2,z3,z4,z6]),(0,[z0,z237,z1,z2,z3,z4,z6])],[(0,[z64,z0,z1,z2,z3,z4,z6]),(0,[z15,z0,z1,z11,z3,z4,z6]),(0,[z238,z0,z1,z2,z3,z4,z6])],[(0,[z101,z0,z1,z2,z4,z112,z6]),(0,[z0,z239,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z187]),(0,[z0,z1,z2,z3,z4,z6,z240]),(0,[z0,z2,z3,z116,z4,z241,z6])],[(0,[z40,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z159,z6])],[(0,[z118,z0,z1,z2,z79,z4,z6]),(0,[z0,z1,z2,z3,z4,z242,z6])],[(0,[z0,z32,z1,z2,z117,z4,z6])],[(0,[z0,z1,z2,z3,z4,z156,z6])]]

def bk0_9 : List (List (ℕ × List W)) :=
  [[],[(0,[z0,z1,z243,z2,z3,z4,z6]),(0,[z0,z1,z244,z2,z3,z4,z6]),(0,[z0,z1,z2,z245,z3,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6])],[(0,[z0,z246,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z29,z3,z4,z70])],[(0,[z0,z1,z130,z2,z3,z4,z6]),(0,[z0,z1,z2,z247,z3,z4,z6])],[(0,[z248,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z112,z6]),(0,[z0,z2,z16,z3,z4,z5,z6]),(0,[z0,z2,z3,z249,z4,z5,z6])],[(0,[z0,z250,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z251,z4,z6]),(1,[z0,z2,z3,z4,z241,z6])],[(0,[z0,z1,z2,z252,z3,z4,z6]),(0,[z0,z1,z2,z3,z253,z4,z6]),(1,[z0,z1,z2,z79,z4,z80])],[(0,[z254,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z255,z4,z6]),(1,[z0,z1,z2,z3,z256,z6])],[(0,[z0,z257,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z117,z4,z6])],[(0,[z0,z258,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z38,z4,z5,z6])],[(0,[z0,z1,z2,z259,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z260])],[],[(1,[z0,z261,z2,z3,z4,z6])],[(0,[z0,z83,z2,z3,z4,z5,z6])],[(0,[z0,z9,z124,z2,z3,z4,z6]),(0,[z0,z262,z1,z2,z3,z4,z6]),(0,[z0,z1,z263,z2,z3,z4,z6]),(0,[z0,z1,z2,z264,z3,z4,z6]),(0,[z0,z1,z2,z265,z3,z4,z6]),(0,[z0,z1,z2,z3,z266,z4,z6]),(0,[z0,z1,z2,z3,z267,z4,z6]),(0,[z0,z2,z3,z4,z5,z75,z6]),(1,[z268,z1,z2,z3,z4,z6])],[(0,[z0,z1,z269,z2,z3,z4,z6])]]

def bk0_10 : List (List (ℕ × List W)) :=
  [[(0,[z270,z0,z1,z2,z3,z4,z6]),(0,[z24,z0,z1,z2,z79,z3,z4])],[(0,[z40,z0,z1,z2,z271,z4,z6]),(0,[z272,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z273,z2,z3,z4,z6]),(0,[z0,z1,z274,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z275,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z276])],[(0,[z0,z1,z2,z3,z4,z6,z277])],[(0,[z0,z174,z1,z83,z3,z4,z6])],[(0,[z0,z1,z2,z3,z278,z4,z6]),(1,[z0,z2,z3,z4,z178,z6])],[(0,[z24,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z16,z3,z4,z6]),(0,[z0,z1,z279,z2,z3,z4,z6])],[(0,[z280,z0,z1,z2,z3,z4,z6]),(0,[z0,z281,z1,z2,z3,z4,z6])],[],[(0,[z0,z175,z1,z2,z3,z4,z6]),(0,[z0,z1,z282,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z283,z4,z6]),(0,[z0,z1,z2,z3,z284,z4,z6]),(0,[z0,z1,z2,z3,z4,z285,z6])],[(0,[z0,z9,z2,z3,z4,z6,z147]),(0,[z0,z1,z2,z3,z4,z286,z6]),(0,[z0,z2,z3,z169,z4,z287,z6])],[(0,[z0,z1,z114,z2,z3,z4,z6]),(0,[z0,z1,z2,z288,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z289,z6])],[(0,[z101,z0,z1,z2,z38,z4,z6])],[(0,[z24,z0,z1,z59,z2,z3,z4]),(0,[z0,z154,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z290,z3,z4,z6]),(0,[z0,z1,z2,z3,z291,z4,z6]),(0,[z0,z1,z2,z3,z4,z241,z6])],[(0,[z0,z1,z2,z3,z292,z4,z6])],[],[]]

def bk0_11 : List (List (ℕ × List W)) :=
  [[(0,[z62,z0,z1,z3,z4,z156,z6])],[(0,[z0,z1,z2,z3,z4,z6,z293]),(0,[z1,z2,z3,z4,z25,z6,z50])],[],[],[(0,[z0,z9,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z38,z4,z6]),(0,[z0,z294,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z295,z6]),(1,[z0,z1,z2,z296,z3,z4])],[(0,[z0,z1,z2,z3,z297,z4,z6]),(0,[z0,z1,z2,z3,z7,z4,z6])],[(0,[z0,z9,z11,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z298,z6])],[(0,[z299,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z300,z3,z4,z6]),(0,[z0,z1,z2,z301,z3,z4,z6])],[(0,[z0,z1,z302,z2,z3,z4,z6]),(0,[z0,z1,z2,z303,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z304,z6]),(0,[z0,z1,z2,z3,z4,z6,z305])],[(0,[z306,z0,z1,z2,z3,z4,z6]),(0,[z307,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z308]),(0,[z1,z114,z2,z16,z3,z4,z6]),(1,[z0,z1,z2,z309,z4,z6])],[(0,[z8,z0,z1,z2,z3,z4,z6]),(0,[z0,z55,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z19,z4,z5,z6])],[(0,[z0,z1,z310,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z311,z4,z6]),(0,[z0,z1,z2,z3,z4,z178,z6])],[(0,[z101,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z312,z4,z6])],[(0,[z0,z1,z2,z271,z3,z4,z6]),(0,[z0,z1,z2,z3,z313,z4,z6]),(0,[z0,z1,z2,z3,z4,z314,z6])],[(0,[z315,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z75,z69]),(0,[z0,z2,z3,z4,z5,z6,z69])],[(0,[z316,z0,z1,z2,z3,z4,z6])]]

def bk0_12 : List (List (ℕ × List W)) :=
  [[(1,[z0,z2,z3,z4,z287,z6])],[(0,[z0,z1,z2,z3,z4,z6,z317])],[(0,[z62,z0,z318,z2,z3,z4,z6]),(0,[z0,z9,z63,z2,z3,z4,z6]),(0,[z0,z89,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z319,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z320])],[(0,[z321,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z322,z2,z3,z4,z6])],[(0,[z0,z1,z59,z2,z3,z4,z112]),(0,[z0,z1,z2,z3,z323,z4,z6])],[(0,[z0,z9,z2,z3,z4,z75,z6]),(0,[z0,z1,z2,z324,z3,z4,z6]),(0,[z0,z1,z2,z3,z325,z4,z6])],[(0,[z0,z32,z2,z117,z3,z4,z6]),(0,[z0,z1,z2,z3,z66,z4,z6]),(0,[z0,z1,z2,z3,z326,z4,z6]),(0,[z0,z1,z2,z3,z4,z181,z6])],[(0,[z327,z0,z1,z2,z3,z4,z6]),(0,[z88,z0,z2,z3,z4,z5,z6]),(0,[z0,z9,z2,z79,z3,z4,z6]),(0,[z0,z1,z2,z29,z3,z6,z69])],[],[(0,[z109,z0,z85,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z159,z6])],[(0,[z0,z328,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z84,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z329]),(0,[z0,z1,z2,z3,z4,z6,z330])],[(0,[z189,z0,z2,z3,z4,z5,z6]),(0,[z0,z9,z1,z2,z3,z66,z6]),(0,[z0,z1,z2,z331,z3,z4,z6]),(1,[z0,z1,z2,z3,z125,z6])],[(0,[z0,z332,z1,z2,z3,z4,z6]),(0,[z0,z333,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z334,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z156,z6])],[]]

def bk0_13 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z335,z3,z4,z6])],[],[(0,[z0,z1,z2,z336,z3,z4,z6])],[(0,[z0,z1,z337,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z25,z6]),(0,[z0,z1,z2,z3,z4,z25,z80])],[(1,[z0,z338,z2,z3,z4,z6])],[(0,[z24,z118,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z339])],[(0,[z340,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z29,z3,z4,z5,z6])],[(0,[z0,z1,z341,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z287,z6])],[(0,[z0,z342,z1,z2,z3,z4,z6]),(0,[z0,z1,z343,z2,z3,z4,z6])],[(0,[z40,z0,z1,z2,z3,z4,z6])],[(0,[z0,z9,z2,z3,z22,z4,z6])],[],[(0,[z344,z0,z1,z2,z3,z4,z6]),(0,[z0,z345,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z249,z4,z6]),(0,[z0,z1,z2,z3,z4,z346,z6])],[(0,[z347,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z348,z3,z4,z6]),(0,[z0,z1,z2,z3,z349,z4,z6]),(0,[z0,z1,z2,z3,z4,z350,z6])],[(0,[z109,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z351,z6])]]

def bk0_14 : List (List (ℕ × List W)) :=
  [[(0,[z0,z352,z1,z2,z3,z4,z6]),(0,[z0,z1,z353,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z276])],[(0,[z0,z1,z2,z3,z354,z4,z6])],[(1,[z0,z1,z2,z355,z4,z6])],[(0,[z356,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z357,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z358]),(1,[z0,z2,z3,z23,z5,z6])],[(0,[z359,z0,z1,z2,z3,z4,z6]),(0,[z0,z318,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z66,z169,z6])],[(0,[z101,z0,z2,z3,z4,z5,z6])],[(0,[z0,z1,z360,z2,z3,z4,z6])],[(0,[z0,z361,z1,z2,z3,z4,z6])],[(0,[z362,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z363,z6])],[(0,[z0,z1,z2,z3,z4,z6,z364])],[(0,[z0,z1,z2,z3,z365,z4,z6])],[(0,[z0,z366,z1,z2,z3,z4,z6]),(0,[z0,z1,z367,z2,z3,z4,z6]),(0,[z0,z1,z2,z368,z3,z4,z6]),(0,[z0,z1,z2,z3,z369,z4,z6])],[(0,[z0,z1,z2,z3,z4,z370,z6])],[],[(0,[z371,z0,z2,z3,z4,z5,z6]),(0,[z0,z372,z1,z2,z3,z4,z6])],[]]

def bk0_15 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z3,z4,z373,z6]),(0,[z0,z1,z2,z3,z4,z6,z374])],[],[(0,[z0,z1,z2,z3,z4,z375,z6]),(0,[z0,z1,z2,z3,z4,z6,z376])],[(0,[z87,z0,z261,z2,z3,z4,z6]),(0,[z0,z1,z2,z377,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z112,z50])],[(0,[z0,z378,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z134,z4,z6])],[(0,[z10,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z216,z2,z3,z4,z70])],[(0,[z62,z0,z1,z2,z37,z4,z6]),(0,[z0,z379,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z380,z6]),(0,[z0,z1,z2,z3,z4,z6,z381])],[(0,[z382,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z383,z4,z6])],[(0,[z0,z32,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z19,z4,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z102,z3,z4,z25,z6])],[(0,[z384,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z33,z6])],[(0,[z0,z1,z2,z3,z4,z385,z6]),(0,[z0,z1,z2,z3,z23,z5,z6])],[(0,[z0,z386,z55,z2,z3,z4,z6])],[],[(0,[z62,z0,z1,z2,z3,z156,z6]),(0,[z0,z9,z2,z16,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z387,z6])],[(0,[z10,z1,z2,z3,z4,z23,z6]),(0,[z0,z9,z2,z3,z169,z4,z6]),(0,[z0,z1,z59,z2,z79,z4,z6])],[(0,[z0,z388,z1,z2,z3,z4,z6])]]

def bk0_16 : List (List (ℕ × List W)) :=
  [[(0,[z88,z1,z2,z3,z22,z4,z6]),(0,[z0,z1,z185,z216,z3,z4,z6])],[(0,[z389,z0,z1,z2,z3,z4,z6]),(0,[z390,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z391,z4,z6]),(0,[z0,z1,z2,z3,z392,z4,z6])],[(0,[z0,z1,z2,z3,z393,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z394]),(0,[z0,z1,z2,z3,z4,z6,z395]),(0,[z0,z1,z2,z3,z4,z6,z396]),(0,[z0,z18,z2,z3,z4,z5,z6])],[(0,[z8,z1,z2,z3,z4,z25,z6]),(0,[z0,z9,z59,z2,z3,z4,z6]),(0,[z0,z2,z79,z3,z4,z5,z6])],[(0,[z0,z148,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z397,z4,z6])],[(0,[z62,z0,z9,z2,z3,z4,z6]),(0,[z0,z55,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z398,z4,z6])],[(0,[z109,z0,z2,z3,z4,z5,z6]),(0,[z0,z399,z1,z2,z3,z4,z6]),(0,[z0,z1,z400,z2,z3,z4,z6]),(0,[z0,z1,z401,z2,z3,z4,z6]),(0,[z0,z1,z2,z402,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z403,z6])],[(0,[z0,z1,z404,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z405,z6]),(1,[z406,z1,z2,z3,z4,z6]),(1,[z0,z124,z2,z3,z4,z159])],[(0,[z0,z407,z9,z2,z3,z4,z6])],[(0,[z0,z1,z408,z2,z3,z4,z6])],[],[(0,[z0,z55,z1,z2,z60,z4,z6])],[(0,[z0,z124,z2,z3,z4,z5,z6]),(0,[z0,z2,z409,z3,z4,z5,z6])],[(0,[z410,z0,z1,z2,z3,z4,z6]),(0,[z0,z32,z1,z2,z3,z7,z6])]]

def bk0_17 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z411,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z412])],[(0,[z0,z1,z2,z3,z4,z413,z6])],[(0,[z0,z1,z131,z2,z21,z4,z6]),(0,[z0,z1,z414,z2,z3,z4,z6]),(0,[z0,z1,z2,z134,z3,z4,z6]),(0,[z0,z1,z2,z415,z3,z4,z6]),(0,[z0,z2,z201,z16,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z25,z6])],[],[(0,[z416,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z417]),(0,[z0,z1,z2,z3,z4,z6,z418])],[(0,[z101,z0,z1,z2,z102,z4,z6]),(0,[z88,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z29,z3,z4,z6]),(0,[z0,z1,z2,z3,z56,z4,z6])],[(0,[z419,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z154,z2,z3,z4,z6]),(0,[z0,z420,z1,z2,z3,z4,z6])],[(0,[z421,z0,z1,z2,z3,z4,z6])],[(0,[z109,z0,z83,z2,z3,z4,z6])],[(0,[z422,z0,z1,z2,z3,z4,z6]),(0,[z0,z423,z1,z2,z3,z4,z6]),(0,[z0,z1,z424,z2,z3,z4,z6]),(0,[z0,z1,z2,z2,z3,z4,z6])],[(0,[z189,z0,z1,z2,z3,z4,z6]),(0,[z425,z0,z1,z2,z3,z4,z6]),(0,[z0,z11,z2,z3,z4,z5,z6])],[(0,[z0,z426,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z427,z3,z4,z6]),(0,[z0,z1,z2,z3,z116,z4,z69])],[(0,[z0,z428,z1,z2,z3,z4,z6]),(0,[z0,z1,z429,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z430,z6])],[(0,[z431,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z432,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z433,z6])],[(0,[z10,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z18,z2,z21,z4,z6]),(0,[z0,z1,z2,z434,z3,z4,z6])],[(0,[z435,z0,z1,z2,z3,z4,z6])]]

def bk0_18 : List (List (ℕ × List W)) :=
  [[(0,[z0,z55,z1,z2,z3,z66,z6]),(0,[z0,z436,z1,z2,z3,z4,z6]),(0,[z0,z1,z437,z2,z3,z4,z6]),(0,[z0,z1,z2,z438,z3,z4,z6])],[(0,[z0,z55,z1,z2,z3,z6,z167])],[(0,[z0,z439,z1,z2,z3,z4,z6]),(1,[z0,z440,z2,z3,z4,z6])],[(0,[z88,z1,z2,z16,z3,z4,z6]),(0,[z0,z9,z2,z3,z116,z4,z6]),(0,[z0,z1,z441,z2,z3,z4,z6]),(0,[z0,z1,z2,z442,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z443,z6])],[(0,[z0,z1,z2,z3,z444,z4,z6]),(0,[z0,z1,z2,z3,z4,z155,z70])],[(1,[z41,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z445,z6])],[(0,[z0,z1,z446,z2,z3,z4,z6]),(0,[z0,z1,z447,z2,z3,z4,z6]),(0,[z0,z1,z448,z2,z3,z4,z6]),(0,[z0,z1,z2,z29,z3,z116,z4]),(0,[z0,z1,z2,z3,z4,z449,z6])],[(0,[z450,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z451,z3,z4,z6]),(0,[z0,z185,z2,z3,z4,z5,z6])],[(0,[z0,z9,z2,z3,z4,z6,z69]),(0,[z0,z1,z452,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z50]),(0,[z0,z1,z2,z3,z4,z6,z167]),(0,[z0,z1,z2,z38,z4,z6,z80])],[(0,[z0,z1,z2,z453,z3,z4,z6]),(0,[z0,z1,z2,z3,z454,z4,z6]),(0,[z0,z1,z2,z3,z4,z455,z6])],[(0,[z0,z456,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z457,z4,z6])],[(0,[z0,z1,z2,z3,z4,z458,z6])],[(0,[z0,z1,z459,z2,z3,z4,z6])],[(0,[z15,z0,z1,z16,z3,z4,z6]),(0,[z0,z9,z2,z3,z66,z4,z6]),(0,[z0,z460,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z29,z3,z66,z6]),(1,[z0,z2,z3,z169,z5,z6])],[(0,[z0,z1,z2,z461,z3,z4,z6]),(1,[z0,z1,z2,z462,z4,z6])]]

def bk0_19 : List (List (ℕ × List W)) :=
  [[(0,[z62,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z463,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z464,z4,z6]),(0,[z0,z1,z2,z3,z465,z4,z6])],[],[(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z10,z1,z11,z2,z3,z4,z6]),(0,[z0,z9,z235,z2,z3,z4,z6]),(0,[z0,z1,z2,z466,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z467])],[(0,[z87,z88,z1,z2,z3,z4,z6]),(0,[z0,z9,z148,z2,z3,z4,z6]),(0,[z0,z1,z2,z348,z4,z6,z50]),(0,[z85,z1,z114,z2,z3,z4,z6])],[],[(0,[z468,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z469,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z470]),(1,[z0,z399,z2,z3,z4,z6])],[(0,[z0,z9,z2,z3,z4,z159,z6])],[],[(0,[z471,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z60,z3,z4,z6]),(0,[z0,z1,z2,z56,z4,z6,z167])],[(0,[z472,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z156,z6]),(0,[z0,z124,z1,z2,z3,z4,z155]),(0,[z0,z1,z440,z2,z3,z4,z6]),(0,[z0,z1,z2,z102,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z473,z6]),(1,[z0,z1,z2,z3,z84,z6])],[(0,[z321,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z25,z6]),(0,[z0,z474,z1,z2,z3,z4,z6])],[(0,[z371,z0,z1,z2,z3,z4,z6]),(0,[z0,z475,z1,z2,z3,z4,z6])],[(0,[z36,z0,z85,z2,z3,z4,z6])],[(0,[z476,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z477,z2,z3,z4,z6])],[(0,[z0,z1,z2,z478,z3,z4,z6]),(0,[z0,z1,z2,z3,z479,z4,z6]),(0,[z0,z1,z2,z3,z4,z480,z6])],[(0,[z0,z1,z2,z3,z4,z481,z6])]]

def bk0_20 : List (List (ℕ × List W)) :=
  [[],[(0,[z40,z0,z1,z46,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z482,z6]),(0,[z0,z216,z2,z3,z4,z5,z6])],[(0,[z0,z1,z483,z2,z3,z4,z6]),(0,[z0,z1,z484,z2,z3,z4,z6])],[(0,[z485,z0,z1,z2,z3,z4,z6]),(0,[z486,z0,z1,z2,z3,z4,z6]),(0,[z118,z0,z1,z2,z4,z112,z6]),(0,[z0,z379,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z487,z3,z4,z6]),(0,[z0,z1,z2,z488,z3,z4,z6])],[(0,[z40,z0,z1,z2,z3,z4,z187]),(0,[z0,z1,z2,z3,z489,z4,z6]),(0,[z0,z1,z2,z3,z490,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z491])],[(0,[z0,z32,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z169,z5,z6])],[(0,[z0,z492,z1,z2,z3,z4,z6])],[(0,[z0,z1,z493,z2,z3,z4,z6])],[(0,[z0,z9,z2,z264,z3,z4,z6]),(0,[z0,z1,z2,z4,z494,z6,z50])],[(1,[z0,z1,z2,z3,z91,z6])],[(0,[z0,z1,z2,z495,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z112,z25])],[],[(0,[z0,z1,z496,z2,z3,z4,z6])],[(0,[z0,z1,z2,z497,z3,z4,z6]),(0,[z0,z1,z2,z498,z3,z4,z6]),(0,[z0,z1,z2,z3,z499,z4,z6]),(0,[z0,z1,z2,z3,z4,z142,z6]),(1,[z0,z2,z3,z22,z5,z6])],[(0,[z0,z1,z500,z2,z3,z4,z6])],[(0,[z0,z1,z501,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z3,z4,z6])]]

def bk0_21 : List (List (ℕ × List W)) :=
  [[(0,[z502,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z6,z503])],[(0,[z36,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z60,z3,z66,z6]),(0,[z0,z1,z2,z3,z4,z504,z6]),(0,[z0,z1,z2,z3,z4,z6,z505]),(1,[z0,z1,z2,z4,z494,z6])],[(0,[z506,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z60,z3,z6,z167]),(0,[z0,z1,z2,z3,z507,z4,z6]),(0,[z0,z1,z2,z3,z508,z4,z6]),(0,[z0,z1,z2,z3,z4,z509,z6])],[(0,[z62,z0,z1,z2,z3,z4,z45]),(0,[z0,z510,z1,z2,z3,z4,z6]),(0,[z0,z148,z1,z2,z3,z4,z6]),(0,[z0,z1,z63,z3,z169,z4,z6]),(0,[z0,z1,z2,z3,z511,z4,z6]),(1,[z0,z2,z3,z116,z5,z6])],[(0,[z347,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z114,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z512,z6])],[(0,[z109,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z513,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z60,z4,z6]),(0,[z0,z1,z2,z3,z514,z4,z6]),(0,[z0,z1,z3,z4,z75,z6,z70])],[(0,[z87,z0,z1,z2,z3,z23,z6]),(0,[z0,z515,z1,z2,z3,z4,z6]),(0,[z0,z1,z516,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z6,z517])],[(0,[z0,z518,z1,z2,z3,z4,z6])],[(0,[z0,z1,z519,z2,z3,z4,z6]),(0,[z0,z1,z2,z520,z3,z4,z6])],[],[(0,[z0,z1,z521,z2,z3,z4,z6])],[(0,[z0,z124,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z522])],[(0,[z0,z55,z1,z2,z4,z6,z167]),(0,[z0,z1,z523,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z524,z6]),(0,[z0,z2,z3,z56,z4,z5,z6]),(1,[z0,z174,z83,z3,z4,z6])],[(0,[z525,z0,z1,z2,z3,z4,z6]),(0,[z0,z261,z1,z2,z3,z4,z6])],[(1,[z62,z0,z1,z3,z156,z6])],[(0,[z62,z72,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z526,z6])]]

def bk0_22 : List (List (ℕ × List W)) :=
  [[(0,[z527,z0,z1,z2,z3,z4,z6]),(0,[z0,z528,z1,z2,z3,z4,z6])],[(0,[z0,z338,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z529,z6])],[(0,[z101,z118,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z530,z4,z6]),(0,[z0,z1,z2,z3,z4,z531,z6])],[(0,[z40,z36,z0,z2,z3,z4,z6]),(0,[z118,z0,z1,z2,z38,z4,z6]),(0,[z109,z1,z2,z16,z3,z4,z6])],[(0,[z0,z1,z2,z3,z22,z5,z6]),(1,[z0,z2,z3,z4,z532,z6])],[(0,[z0,z1,z2,z3,z4,z6,z533]),(0,[z0,z1,z3,z169,z4,z156,z6]),(0,[z0,z131,z2,z3,z4,z5,z6])],[],[(0,[z0,z1,z2,z3,z534,z4,z6]),(0,[z0,z1,z2,z3,z4,z535,z6])],[(0,[z536,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z50]),(0,[z0,z2,z3,z4,z5,z6,z167])],[(0,[z0,z1,z2,z3,z61,z4,z6])],[(0,[z0,z1,z2,z79,z4,z6,z80]),(0,[z0,z1,z2,z3,z116,z5,z6])],[(0,[z24,z0,z1,z2,z309,z4,z6]),(0,[z10,z0,z1,z2,z3,z4,z6])],[(0,[z537,z0,z1,z2,z3,z4,z6]),(0,[z0,z148,z1,z2,z3,z66,z6]),(0,[z0,z538,z1,z2,z3,z4,z6]),(0,[z0,z1,z539,z2,z3,z4,z6]),(0,[z1,z11,z2,z16,z3,z4,z6]),(1,[z486,z0,z2,z3,z4,z6]),(1,[z0,z1,z2,z37,z4,z6])],[],[(0,[z540,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z541,z4,z6]),(1,[z0,z386,z2,z3,z4,z6])],[(0,[z542,z0,z1,z2,z3,z4,z6]),(0,[z0,z543,z1,z2,z3,z4,z6])]]

def bk0_23 : List (List (ℕ × List W)) :=
  [[(0,[z544,z0,z1,z2,z3,z4,z6]),(0,[z545,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z256,z6]),(0,[z0,z1,z2,z3,z4,z546,z6])],[(0,[z547,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z548,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z549,z6])],[(0,[z0,z1,z2,z3,z4,z6,z550])],[(0,[z268,z1,z2,z3,z4,z6,z80])],[(0,[z118,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z185,z2,z3,z4,z70]),(0,[z0,z1,z2,z551,z3,z4,z6])],[(0,[z0,z1,z552,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z553])],[(0,[z554,z0,z1,z2,z3,z4,z6]),(0,[z88,z10,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z4,z6]),(0,[z0,z555,z1,z2,z3,z4,z6]),(1,[z0,z556,z2,z3,z4,z6])],[(0,[z557,z0,z1,z2,z3,z4,z6]),(0,[z0,z41,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z558,z4,z6]),(0,[z0,z1,z2,z3,z4,z559,z6]),(1,[z0,z1,z195,z2,z3,z4])],[(0,[z0,z1,z216,z2,z3,z4,z6]),(0,[z0,z1,z560,z2,z3,z4,z6]),(0,[z0,z1,z2,z561,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z562]),(0,[z1,z2,z3,z4,z6,z517,z80])],[(0,[z0,z1,z2,z60,z56,z4,z6]),(0,[z0,z2,z3,z4,z159,z6,z155])],[],[(0,[z0,z1,z18,z3,z19,z4,z6]),(0,[z0,z1,z563,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z532,z6]),(1,[z0,z318,z2,z3,z4,z6])],[(0,[z109,z85,z1,z2,z3,z4,z6]),(0,[z0,z564,z1,z2,z3,z4,z6]),(1,[z0,z2,z3,z5,z156,z6])],[(0,[z62,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z480,z6]),(1,[z0,z9,z2,z3,z4,z6])],[(0,[z15,z0,z9,z2,z3,z4,z6]),(0,[z565,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z566,z4,z6])],[(0,[z118,z0,z1,z2,z3,z4,z550]),(0,[z0,z1,z2,z3,z567,z4,z6]),(0,[z0,z1,z2,z3,z4,z192,z6])]]

def bk0_24 : List (List (ℕ × List W)) :=
  [[(0,[z0,z568,z9,z2,z3,z4,z6]),(0,[z0,z17,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z355,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z569])],[(0,[z0,z386,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z46,z3,z4,z6])],[],[(0,[z0,z570,z1,z2,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z116,z6]),(0,[z0,z1,z2,z571,z3,z4,z6]),(0,[z0,z1,z2,z572,z3,z4,z6])],[(0,[z573,z0,z1,z2,z3,z4,z6]),(0,[z574,z0,z1,z2,z3,z4,z6]),(0,[z0,z575,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z576,z6]),(0,[z0,z577,z2,z3,z4,z5,z6])],[],[(0,[z0,z1,z577,z2,z3,z4,z6]),(1,[z109,z85,z2,z3,z4,z6])],[(0,[z0,z1,z578,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z550])],[(0,[z8,z24,z1,z2,z3,z4,z6]),(0,[z24,z1,z2,z3,z4,z6,z50])],[(0,[z10,z109,z1,z2,z3,z4,z6]),(0,[z0,z579,z1,z2,z3,z4,z6])],[(0,[z0,z12,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z75,z159])],[(0,[z486,z0,z2,z16,z3,z4,z6]),(0,[z0,z1,z2,z4,z112,z6,z80])],[(0,[z40,z0,z174,z2,z3,z4,z6]),(0,[z10,z1,z114,z2,z3,z4,z6]),(0,[z0,z580,z1,z2,z3,z4,z6]),(0,[z0,z1,z556,z2,z3,z4,z6])],[(0,[z40,z0,z1,z83,z3,z4,z6]),(0,[z581,z0,z1,z2,z3,z4,z6])],[(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z583,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z584,z3,z4,z6]),(0,[z0,z2,z3,z169,z4,z5,z6])]]

def bk0_25 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z131,z2,z3,z4,z6]),(0,[z0,z1,z585,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z586,z4,z6]),(0,[z0,z1,z2,z3,z4,z587,z6]),(0,[z0,z1,z2,z3,z4,z132,z6])],[(0,[z0,z588,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z589,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z6,z590])],[(0,[z0,z1,z591,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z592]),(0,[z0,z1,z2,z3,z4,z6,z593])],[(0,[z0,z1,z2,z3,z594,z4,z6])],[(0,[z595,z0,z1,z2,z3,z4,z6]),(1,[z0,z9,z2,z3,z66,z6])],[],[],[(0,[z24,z1,z2,z102,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z596])],[(0,[z62,z0,z1,z2,z3,z169,z6]),(0,[z62,z0,z1,z2,z3,z4,z54]),(0,[z0,z89,z1,z2,z61,z4,z6]),(0,[z0,z1,z2,z3,z309,z4,z6])],[],[(0,[z0,z1,z597,z2,z3,z4,z6]),(0,[z0,z1,z18,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z598,z4,z6]),(0,[z0,z2,z3,z116,z4,z5,z6]),(1,[z118,z1,z2,z38,z4,z6])],[(0,[z502,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z70])],[(0,[z599,z0,z1,z2,z3,z4,z6]),(0,[z0,z600,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z60,z19,z4,z6])]]

def bk0_26 : List (List (ℕ × List W)) :=
  [[(0,[z0,z601,z1,z2,z3,z4,z6]),(0,[z0,z602,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z603,z4,z6])],[(0,[z604,z0,z1,z2,z3,z4,z6]),(0,[z0,z174,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z605,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z606,z6])],[(0,[z0,z9,z2,z3,z19,z4,z6])],[(0,[z0,z1,z2,z607,z3,z4,z6]),(0,[z0,z1,z2,z3,z608,z4,z6])],[(0,[z0,z9,z32,z2,z3,z4,z6]),(0,[z0,z1,z2,z21,z4,z6,z167]),(0,[z0,z2,z3,z4,z5,z6,z533])],[(0,[z0,z9,z43,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z609,z6]),(0,[z0,z1,z2,z61,z19,z4,z6]),(1,[z0,z2,z3,z4,z5,z6])],[(0,[z15,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z46,z3,z4,z5,z6])],[(0,[z0,z1,z2,z3,z610,z4,z6]),(0,[z0,z1,z2,z3,z611,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z517])],[],[(0,[z0,z1,z612,z2,z3,z4,z6])],[(0,[z0,z9,z174,z2,z3,z4,z6])],[],[],[(0,[z613,z0,z1,z2,z3,z4,z6]),(0,[z24,z0,z1,z2,z3,z4,z50]),(0,[z614,z0,z1,z2,z3,z4,z6])],[(0,[z118,z1,z2,z3,z38,z4,z6]),(0,[z0,z1,z2,z409,z3,z4,z6])]]

def bk0_27 : List (List (ℕ × List W)) :=
  [[(0,[z100,z0,z9,z2,z3,z4,z6]),(0,[z0,z43,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z615,z6])],[(0,[z616,z0,z1,z2,z3,z4,z6]),(0,[z0,z617,z1,z2,z3,z4,z6]),(0,[z0,z174,z83,z2,z3,z4,z6])],[(0,[z0,z9,z2,z402,z3,z4,z6])],[],[(0,[z0,z1,z618,z2,z3,z4,z6]),(0,[z0,z1,z59,z2,z4,z112,z6])],[(0,[z0,z1,z2,z619,z3,z4,z6])],[(0,[z0,z9,z2,z21,z3,z4,z6]),(0,[z0,z399,z43,z2,z3,z4,z6]),(0,[z0,z620,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z462,z3,z4,z6])],[(0,[z0,z1,z2,z3,z621,z4,z6]),(0,[z0,z1,z2,z3,z4,z622,z6]),(0,[z0,z1,z2,z3,z4,z623,z6])],[],[(0,[z0,z1,z624,z2,z3,z4,z6]),(0,[z0,z1,z2,z625,z3,z4,z6])],[(0,[z0,z43,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z626,z3,z4,z6])],[(0,[z0,z1,z2,z3,z627,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z155]),(1,[z0,z1,z2,z271,z4,z6])],[],[(0,[z36,z0,z2,z3,z4,z5,z6]),(0,[z0,z628,z1,z2,z3,z4,z6])],[(0,[z0,z1,z629,z2,z3,z4,z6])],[(0,[z406,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z29,z3,z4,z6]),(0,[z0,z9,z2,z3,z56,z4,z6])]]

def bk0_28 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z630,z3,z4,z6])],[(1,[z0,z1,z2,z3,z346,z6])],[],[(0,[z62,z0,z130,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z3,z4,z50]),(0,[z0,z407,z1,z2,z3,z4,z6]),(0,[z0,z43,z1,z2,z29,z3,z6])],[(0,[z0,z1,z2,z296,z3,z38,z4]),(0,[z0,z1,z2,z3,z4,z631,z6]),(0,[z0,z2,z21,z3,z4,z5,z6])],[(0,[z0,z1,z632,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z633,z6])],[(0,[z0,z1,z131,z21,z3,z4,z6])],[(0,[z0,z1,z2,z29,z3,z4,z75])],[(0,[z40,z0,z1,z2,z355,z4,z6]),(0,[z634,z0,z1,z2,z3,z4,z6]),(0,[z506,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z635,z4,z6])],[(0,[z40,z0,z1,z2,z3,z4,z358]),(0,[z636,z0,z1,z2,z3,z4,z6]),(0,[z0,z68,z2,z3,z4,z5,z6])],[(0,[z0,z338,z2,z3,z22,z4,z6]),(0,[z0,z1,z637,z2,z3,z4,z6])],[(0,[z0,z1,z638,z2,z3,z4,z6])],[(0,[z0,z1,z2,z639,z3,z4,z6]),(0,[z0,z1,z2,z640,z3,z4,z6]),(0,[z0,z1,z2,z641,z3,z4,z6])],[(0,[z36,z0,z83,z2,z3,z4,z6]),(0,[z87,z0,z556,z2,z3,z4,z6]),(0,[z118,z0,z1,z2,z102,z4,z6]),(0,[z0,z9,z89,z2,z3,z4,z6]),(0,[z0,z642,z1,z2,z3,z4,z6]),(0,[z0,z1,z83,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z643,z4,z6])],[(0,[z0,z1,z2,z3,z4,z358,z6])],[(0,[z0,z1,z644,z2,z3,z4,z6]),(0,[z0,z1,z2,z117,z3,z4,z6])]]

def bk0_29 : List (List (ℕ × List W)) :=
  [[(0,[z645,z0,z1,z2,z3,z4,z6]),(0,[z0,z646,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z647,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z648])],[(0,[z649,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z650,z3,z4,z6]),(0,[z0,z1,z2,z3,z651,z4,z6])],[(0,[z0,z1,z2,z652,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z33,z6]),(0,[z0,z2,z3,z66,z4,z5,z6])],[(0,[z0,z9,z2,z3,z4,z6,z50]),(0,[z0,z9,z2,z3,z4,z6,z167]),(0,[z0,z1,z2,z3,z66,z23,z6]),(0,[z0,z1,z2,z3,z4,z6,z653])],[(0,[z87,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z59,z2,z38,z4,z6])],[(0,[z101,z0,z1,z2,z79,z4,z6]),(0,[z0,z1,z2,z654,z3,z4,z6])],[(0,[z0,z655,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z188,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z656]),(0,[z0,z1,z2,z3,z5,z156,z6])],[(0,[z8,z0,z1,z2,z3,z4,z25]),(0,[z96,z0,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z657,z3,z4,z6])],[(0,[z36,z0,z1,z2,z3,z346,z6]),(0,[z0,z154,z1,z2,z3,z4,z159]),(0,[z0,z1,z2,z3,z633,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z6])],[(0,[z0,z1,z2,z3,z4,z6,z658])],[(0,[z87,z0,z1,z2,z3,z22,z6])],[(0,[z268,z0,z1,z2,z3,z4,z6]),(0,[z659,z0,z1,z2,z3,z4,z6]),(0,[z0,z660,z1,z2,z3,z4,z6]),(0,[z0,z1,z63,z2,z3,z156,z6]),(0,[z0,z1,z2,z3,z4,z661,z6])],[(0,[z36,z0,z1,z2,z3,z633,z6]),(0,[z0,z2,z60,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z70])],[(0,[z0,z124,z2,z3,z4,z159,z6]),(0,[z0,z662,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z663,z3,z4,z6])],[(0,[z664,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z665,z4,z6])],[(0,[z0,z9,z216,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z666,z6])]]

def bk0_30 : List (List (ℕ × List W)) :=
  [[(0,[z62,z175,z1,z2,z3,z4,z6]),(0,[z118,z0,z2,z3,z4,z5,z6]),(0,[z0,z667,z1,z2,z3,z4,z6]),(0,[z0,z1,z668,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z669,z6])],[(0,[z24,z0,z1,z2,z462,z4,z6])],[(0,[z0,z176,z9,z2,z3,z4,z6]),(0,[z0,z9,z2,z60,z3,z4,z6]),(0,[z0,z1,z2,z670,z3,z4,z6])],[(0,[z671,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z102,z3,z4,z6]),(0,[z0,z1,z2,z672,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z673,z6])],[(0,[z0,z43,z78,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z674])],[(0,[z0,z675,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z676,z4,z6])],[],[(0,[z677,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z216,z2,z3,z4,z75]),(0,[z0,z1,z2,z678,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z679])],[(0,[z0,z9,z1,z2,z3,z5,z6]),(0,[z0,z1,z680,z2,z3,z4,z6])],[(0,[z40,z109,z0,z2,z3,z4,z6]),(0,[z681,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z682,z6]),(0,[z0,z2,z117,z3,z61,z4,z6])],[(0,[z0,z683,z1,z2,z3,z4,z6]),(0,[z0,z1,z684,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z112,z6]),(0,[z0,z2,z3,z22,z4,z532,z6])],[],[],[(0,[z0,z1,z2,z296,z3,z4,z6])],[(0,[z685,z0,z1,z2,z3,z4,z6]),(0,[z0,z174,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z686,z4,z6])],[(0,[z40,z406,z1,z2,z3,z4,z6]),(0,[z0,z1,z687,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z688,z4,z6]),(0,[z0,z1,z2,z3,z4,z689,z6]),(0,[z0,z1,z2,z3,z4,z494,z6]),(1,[z0,z1,z2,z348,z4,z6]),(1,[z0,z2,z29,z3,z5,z6])]]

def bk0_31 : List (List (ℕ × List W)) :=
  [[],[(0,[z0,z690,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z691,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z692])],[(0,[z0,z1,z2,z3,z4,z6,z693]),(0,[z0,z2,z3,z4,z23,z5,z6])],[(0,[z694,z0,z1,z2,z3,z4,z6]),(0,[z0,z55,z440,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z6])],[(0,[z15,z0,z1,z2,z3,z4,z6]),(0,[z0,z695,z1,z2,z3,z4,z6])],[(0,[z109,z0,z114,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z696,z6]),(1,[z0,z76,z2,z3,z4,z6])],[(0,[z0,z568,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z697,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z698,z6])],[(0,[z699,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z185,z2,z3,z4,z6]),(0,[z0,z1,z131,z2,z19,z4,z6])],[(0,[z0,z55,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z4,z700,z6])],[(0,[z0,z135,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z75,z155]),(0,[z0,z1,z2,z3,z4,z701,z6]),(0,[z0,z2,z3,z4,z5,z6,z155])],[(0,[z0,z2,z3,z61,z4,z5,z6])],[(0,[z0,z9,z2,z3,z507,z4,z6]),(0,[z0,z1,z702,z2,z3,z4,z6]),(0,[z0,z1,z703,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z704,z6]),(0,[z0,z1,z2,z3,z4,z705,z6])],[(0,[z87,z0,z2,z3,z4,z5,z6])],[(0,[z0,z1,z706,z2,z3,z4,z6])],[(0,[z0,z124,z1,z2,z3,z256,z6]),(0,[z0,z1,z2,z60,z3,z56,z6])]]

def bk0 : List (List (List (ℕ × List W))) :=
  [bk0_0, bk0_1, bk0_2, bk0_3, bk0_4, bk0_5, bk0_6, bk0_7, bk0_8, bk0_9, bk0_10, bk0_11, bk0_12, bk0_13, bk0_14, bk0_15, bk0_16, bk0_17, bk0_18, bk0_19, bk0_20, bk0_21, bk0_22, bk0_23, bk0_24, bk0_25, bk0_26, bk0_27, bk0_28, bk0_29, bk0_30, bk0_31]

def bk1_0 : List (List (ℕ × List W)) :=
  [[],[(0,[z96,z2,z3,z4,z192,z6]),(0,[z0,z2,z355,z4,z5,z6])],[(0,[z0,z9,z2,z707,z4,z6]),(0,[z0,z2,z3,z14,z5,z6]),(0,[z708,z2,z3,z4,z5,z6])],[(0,[z0,z1,z2,z3,z4,z709]),(0,[z0,z710,z2,z3,z4,z6])],[],[],[(0,[z0,z1,z2,z3,z711,z6]),(0,[z0,z440,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z712]),(0,[z0,z1,z2,z3,z4,z713])],[(0,[z486,z109,z2,z3,z4,z6]),(0,[z0,z9,z2,z714,z4,z6])],[(0,[z0,z1,z2,z3,z4,z715]),(0,[z0,z1,z2,z355,z4,z6]),(0,[z0,z2,z3,z4,z716,z6]),(0,[z41,z1,z2,z3,z4,z6])],[(0,[z118,z9,z2,z38,z4,z6]),(0,[z0,z43,z2,z29,z3,z5]),(0,[z0,z1,z717,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z358]),(0,[z0,z1,z2,z3,z718,z6])],[(0,[z118,z1,z2,z296,z3,z4]),(0,[z0,z719,z2,z3,z4,z6])],[],[(0,[z0,z720,z2,z3,z4,z6]),(0,[z0,z76,z2,z3,z5,z6]),(0,[z0,z26,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z721,z6]),(0,[z1,z2,z102,z4,z25,z80])],[(0,[z100,z0,z2,z3,z4,z132]),(0,[z0,z2,z3,z346,z5,z6]),(0,[z0,z2,z3,z696,z5,z6]),(0,[z2,z3,z4,z5,z722,z6])],[(0,[z723,z1,z2,z3,z4,z6])]]

def bk1_1 : List (List (ℕ × List W)) :=
  [[(0,[z118,z1,z2,z309,z4,z6]),(0,[z0,z724,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z296,z309,z4]),(0,[z0,z2,z3,z169,z5,z6])],[(0,[z0,z1,z2,z3,z4,z725])],[(0,[z0,z338,z2,z3,z66,z6]),(0,[z0,z1,z2,z726,z3,z4])],[(0,[z118,z1,z2,z38,z4,z550]),(0,[z0,z9,z2,z3,z4,z727]),(0,[z0,z728,z2,z3,z4,z6]),(0,[z0,z729,z2,z3,z4,z6]),(0,[z0,z730,z2,z3,z4,z6])],[(0,[z0,z32,z2,z117,z33,z6])],[(0,[z0,z543,z2,z117,z4,z6]),(0,[z0,z68,z2,z3,z4,z159]),(0,[z0,z2,z79,z4,z5,z80])],[(0,[z0,z1,z731,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z732]),(0,[z0,z733,z2,z3,z4,z6])],[],[(0,[z0,z2,z3,z734,z5,z6])],[(0,[z0,z735,z2,z3,z4,z6])],[(0,[z574,z0,z1,z2,z79,z4]),(0,[z0,z655,z2,z3,z5,z6]),(0,[z0,z1,z2,z736,z4,z6]),(0,[z0,z1,z2,z737,z4,z6])],[(0,[z0,z9,z2,z37,z4,z6]),(0,[z0,z1,z2,z738,z4,z6])],[(0,[z0,z739,z2,z3,z4,z6])],[(0,[z0,z2,z740,z3,z4,z6]),(0,[z0,z2,z3,z81,z5,z6]),(0,[z0,z2,z3,z4,z5,z550])]]

def bk1_2 : List (List (ℕ × List W)) :=
  [[],[],[(0,[z8,z0,z1,z2,z348,z4])],[(0,[z0,z1,z2,z3,z4,z741])],[(0,[z0,z1,z2,z3,z742,z6]),(0,[z0,z1,z2,z3,z4,z743])],[(0,[z268,z1,z2,z79,z4,z6]),(0,[z268,z1,z2,z79,z4,z80]),(0,[z0,z1,z2,z3,z4,z744])],[],[],[(0,[z10,z2,z3,z23,z5,z6]),(0,[z0,z1,z2,z271,z84,z6])],[(0,[z118,z1,z2,z4,z546,z6]),(0,[z0,z9,z2,z271,z4,z6]),(0,[z0,z1,z2,z3,z745,z6]),(0,[z0,z2,z106,z3,z5,z6])],[],[(0,[z0,z32,z2,z746,z4,z6]),(0,[z0,z1,z2,z3,z4,z747])],[(0,[z0,z568,z2,z507,z4,z6]),(0,[z0,z1,z2,z3,z4,z748])],[],[(0,[z24,z1,z2,z462,z4,z50])],[]]

def bk1_3 : List (List (ℕ × List W)) :=
  [[(0,[z0,z55,z2,z5,z6,z167])],[(0,[z0,z2,z3,z22,z5,z6])],[(0,[z0,z749,z2,z3,z4,z6]),(0,[z0,z750,z2,z3,z4,z6]),(0,[z0,z2,z3,z5,z82,z6])],[(0,[z0,z1,z2,z751,z4,z6]),(0,[z0,z2,z3,z120,z5,z6]),(0,[z0,z2,z3,z5,z86,z6])],[],[(0,[z0,z1,z2,z3,z4,z752])],[(0,[z0,z1,z2,z3,z753,z6]),(0,[z754,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z1,z756,z3,z4,z6])],[(0,[z0,z1,z2,z757,z3,z4]),(0,[z0,z1,z2,z758,z4,z6])],[(0,[z0,z420,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z759,z6])],[(0,[z0,z760,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z761,z6])],[(0,[z0,z1,z2,z762,z4,z6]),(0,[z0,z2,z60,z188,z5,z6]),(0,[z175,z1,z2,z134,z4,z6])],[(0,[z347,z407,z2,z3,z4,z6]),(0,[z0,z135,z2,z3,z125,z6]),(0,[z0,z2,z3,z403,z5,z6])],[(0,[z0,z9,z2,z763,z4,z6]),(0,[z0,z1,z2,z3,z764,z6]),(0,[z1,z2,z3,z4,z765,z6])],[(0,[z0,z2,z222,z3,z5,z6]),(0,[z2,z3,z22,z23,z5,z6])],[(0,[z0,z9,z2,z3,z289,z6]),(0,[z0,z2,z3,z141,z5,z6]),(0,[z0,z2,z3,z125,z5,z6])]]

def bk1_4 : List (List (ℕ × List W)) :=
  [[(0,[z0,z55,z2,z3,z178,z6]),(0,[z0,z1,z2,z296,z4,z80])],[(0,[z0,z766,z2,z3,z4,z6])],[(0,[z62,z0,z1,z3,z156,z6]),(0,[z0,z9,z2,z767,z4,z6])],[(0,[z0,z1,z2,z3,z768,z6]),(0,[z0,z1,z2,z769,z4,z6])],[(0,[z0,z770,z2,z3,z4,z6]),(0,[z0,z771,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z772,z6]),(0,[z0,z577,z3,z4,z181,z6]),(0,[z773,z1,z2,z3,z4,z6]),(1,[z118,z1,z2,z296,z4])],[(0,[z0,z774,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z775,z6])],[(0,[z776,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z532,z6])],[(0,[z118,z2,z38,z4,z5,z6]),(0,[z777,z1,z2,z3,z4,z6])],[],[(0,[z24,z0,z1,z2,z348,z4]),(0,[z0,z1,z2,z3,z778,z6]),(0,[z0,z1,z2,z3,z779,z6]),(0,[z0,z780,z2,z3,z4,z6])],[(0,[z0,z55,z2,z3,z734,z6]),(0,[z0,z781,z2,z3,z4,z6]),(0,[z0,z1,z2,z678,z4,z80]),(0,[z0,z1,z2,z782,z4,z6])],[(0,[z1,z2,z751,z38,z4,z6])],[(0,[z0,z1,z2,z3,z4,z783]),(0,[z0,z2,z3,z4,z784,z6])],[(0,[z0,z1,z2,z102,z4,z550]),(0,[z0,z1,z2,z3,z785,z6]),(0,[z0,z2,z786,z3,z4,z6]),(0,[z708,z1,z2,z3,z4,z6])]]

def bk1_5 : List (List (ℕ × List W)) :=
  [[(0,[z24,z1,z2,z4,z494,z50]),(0,[z0,z1,z3,z4,z6,z787]),(0,[z0,z2,z3,z4,z6,z788])],[],[(0,[z24,z1,z2,z3,z4,z789]),(0,[z0,z1,z790,z3,z4,z6])],[(0,[z791,z1,z2,z3,z4,z6]),(0,[z0,z792,z2,z3,z5,z6]),(0,[z0,z135,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z793,z6]),(0,[z0,z1,z2,z3,z4,z794])],[(0,[z0,z1,z2,z795,z4,z6])],[(0,[z0,z1,z2,z3,z4,z796]),(0,[z0,z2,z3,z170,z5,z6])],[(0,[z0,z797,z2,z3,z4,z6]),(0,[z0,z1,z2,z462,z4,z6])],[(0,[z0,z1,z2,z3,z4,z798])],[(0,[z406,z1,z2,z3,z4,z187]),(0,[z0,z1,z799,z2,z3,z4]),(0,[z0,z2,z3,z666,z5,z6])],[(0,[z0,z379,z2,z60,z5,z6])],[(0,[z0,z556,z2,z3,z4,z6])],[(0,[z62,z0,z1,z3,z156,z45]),(0,[z800,z1,z2,z3,z4,z6]),(0,[z0,z1,z195,z2,z3,z4]),(0,[z0,z1,z2,z3,z801,z6])],[(0,[z0,z399,z2,z3,z4,z6]),(0,[z0,z2,z3,z266,z5,z6]),(0,[z0,z2,z3,z267,z5,z6])],[(0,[z0,z85,z2,z3,z346,z6]),(0,[z0,z2,z3,z4,z802,z6])],[(0,[z0,z803,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z804]),(0,[z0,z2,z3,z5,z31,z6])],[(0,[z62,z0,z1,z3,z156,z54]),(0,[z0,z386,z2,z3,z7,z6]),(0,[z0,z318,z2,z3,z4,z6])]]

def bk1_6 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z3,z805,z6]),(0,[z0,z1,z2,z3,z84,z6])],[(0,[z0,z407,z2,z3,z5,z6]),(0,[z0,z9,z2,z3,z4,z6]),(0,[z0,z130,z2,z134,z4,z6])],[(0,[z0,z76,z2,z3,z84,z6]),(1,[z0,z2,z3,z806,z6])],[(0,[z118,z1,z2,z751,z4,z6]),(0,[z0,z807,z2,z3,z4,z6]),(0,[z2,z16,z3,z23,z5,z6])],[(0,[z808,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z809,z6])],[],[],[(0,[z0,z2,z3,z5,z166,z6])],[(0,[z0,z1,z2,z348,z4,z550]),(0,[z0,z2,z288,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z810])],[(0,[z0,z1,z2,z37,z4,z45])],[(0,[z0,z2,z4,z5,z811,z6])],[(0,[z0,z2,z3,z4,z812,z6])],[(0,[z0,z1,z2,z3,z4,z550])],[(0,[z486,z0,z2,z3,z806,z6]),(0,[z109,z515,z2,z3,z4,z6])],[(0,[z0,z9,z2,z3,z7,z6]),(0,[z0,z2,z3,z249,z4,z276]),(0,[z0,z2,z3,z4,z813,z6])],[(0,[z0,z814,z2,z3,z5,z6]),(0,[z0,z1,z2,z815,z4,z6])]]

def bk1_7 : List (List (ℕ × List W)) :=
  [[(0,[z816,z2,z3,z4,z5,z6]),(0,[z0,z817,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z91,z6])],[(0,[z0,z568,z2,z3,z33,z6]),(0,[z0,z1,z2,z3,z818,z6])],[(0,[z0,z176,z2,z3,z5,z6]),(0,[z0,z9,z2,z3,z346,z6]),(0,[z0,z819,z2,z3,z4,z6])],[(0,[z0,z2,z3,z7,z5,z6]),(0,[z820,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z821,z6]),(0,[z0,z1,z2,z355,z4,z187]),(0,[z0,z2,z29,z3,z249,z5]),(0,[z0,z2,z37,z4,z5,z6])],[(0,[z72,z1,z2,z37,z4,z6]),(0,[z0,z1,z822,z2,z3,z4])],[(0,[z823,z0,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z633,z6])],[],[(0,[z0,z318,z2,z3,z4,z45]),(0,[z0,z1,z2,z707,z4,z6]),(0,[z0,z1,z2,z4,z494,z6])],[],[(0,[z816,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z66,z6]),(0,[z0,z9,z2,z3,z4,z45]),(0,[z0,z2,z3,z116,z5,z6])],[(0,[z62,z0,z3,z5,z156,z6]),(0,[z824,z1,z2,z3,z4,z6])],[(0,[z24,z9,z2,z3,z4,z50]),(0,[z0,z825,z2,z3,z4,z6]),(0,[z0,z318,z2,z3,z4,z54]),(0,[z0,z1,z2,z3,z826,z6]),(0,[z0,z1,z2,z3,z4,z827]),(0,[z0,z1,z2,z828,z4,z6])],[(0,[z1,z2,z3,z4,z6,z517])],[(0,[z0,z1,z2,z714,z4,z6]),(0,[z0,z2,z3,z4,z829,z6])],[(0,[z0,z2,z3,z256,z159,z6])]]

def bk1_8 : List (List (ℕ × List W)) :=
  [[(0,[z830,z9,z2,z3,z4,z6])],[(0,[z0,z831,z2,z3,z4,z6])],[],[(0,[z0,z174,z83,z3,z4,z6]),(0,[z0,z2,z3,z323,z5,z6])],[(0,[z72,z318,z2,z3,z4,z6])],[(0,[z0,z660,z2,z3,z4,z159]),(0,[z1,z2,z79,z4,z517,z80])],[(0,[z72,z9,z2,z3,z4,z6]),(0,[z0,z2,z832,z3,z4,z6]),(0,[z0,z2,z3,z375,z5,z6]),(0,[z0,z2,z3,z39,z5,z6])],[],[],[(0,[z0,z833,z2,z3,z4,z6])],[(0,[z118,z1,z2,z296,z38,z4]),(0,[z0,z2,z3,z5,z211,z6])],[(0,[z268,z1,z2,z309,z4,z6]),(0,[z0,z1,z2,z3,z4,z727]),(0,[z0,z83,z3,z4,z181,z6])],[(0,[z0,z1,z2,z3,z4,z834])],[(0,[z634,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z835,z4,z6])],[(0,[z0,z2,z335,z3,z5,z6])],[(0,[z0,z9,z2,z3,z385,z6]),(0,[z0,z1,z2,z3,z4,z836])]]

def bk1_9 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z5,z218,z6])],[(0,[z0,z124,z2,z3,z256,z159]),(0,[z1,z2,z102,z309,z4,z6])],[],[(0,[z486,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z37,z4,z6]),(0,[z0,z2,z29,z3,z5,z70])],[],[(0,[z62,z72,z1,z3,z156,z6]),(0,[z0,z386,z2,z3,z4,z6]),(0,[z0,z341,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z837,z6])],[(0,[z87,z2,z3,z23,z5,z6]),(0,[z0,z9,z2,z3,z4,z838]),(0,[z0,z68,z2,z77,z3,z4])],[(0,[z0,z2,z3,z253,z5,z6])],[],[(0,[z0,z1,z2,z4,z6,z804]),(0,[z0,z1,z839,z3,z4,z6])],[],[],[(0,[z0,z1,z840,z2,z3,z4]),(0,[z0,z1,z2,z3,z841,z6]),(0,[z0,z2,z309,z4,z5,z6])],[(0,[z0,z1,z2,z842,z4,z6])],[(0,[z0,z2,z3,z66,z742,z6])],[(0,[z0,z568,z2,z3,z5,z6]),(0,[z0,z1,z2,z271,z4,z6]),(0,[z0,z2,z264,z3,z5,z6]),(0,[z1,z2,z3,z4,z6,z843])]]

def bk1_10 : List (List (ℕ × List W)) :=
  [[(0,[z0,z9,z2,z348,z4,z6]),(0,[z0,z844,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z845,z6])],[(0,[z62,z0,z1,z3,z846,z6]),(0,[z0,z2,z3,z275,z5,z6])],[(0,[z0,z2,z3,z4,z5,z45]),(0,[z0,z2,z3,z5,z156,z6])],[(0,[z0,z1,z2,z3,z4,z847])],[(0,[z24,z2,z3,z4,z5,z50]),(0,[z0,z1,z2,z4,z848,z6])],[(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z2,z3,z4,z159,z743])],[(0,[z0,z1,z2,z850,z4,z6])],[(0,[z0,z9,z2,z3,z627,z6]),(0,[z0,z851,z2,z4,z5,z6]),(0,[z0,z2,z3,z365,z5,z6])],[(0,[z0,z2,z368,z3,z5,z6]),(0,[z0,z2,z3,z284,z5,z6])],[(0,[z0,z1,z2,z852,z3,z4])],[(0,[z0,z853,z2,z3,z4,z6]),(0,[z0,z83,z2,z3,z346,z6])],[],[(0,[z0,z1,z2,z3,z4,z854]),(0,[z0,z1,z3,z4,z846,z6])],[(0,[z109,z85,z2,z3,z4,z6]),(0,[z109,z2,z3,z4,z192,z6]),(0,[z0,z386,z2,z3,z66,z6])],[(0,[z72,z2,z3,z4,z5,z6]),(0,[z0,z855,z2,z3,z4,z6])]]

def bk1_11 : List (List (ℕ × List W)) :=
  [[(0,[z0,z9,z2,z3,z349,z6]),(0,[z0,z856,z2,z3,z4,z6]),(0,[z0,z1,z2,z37,z4,z54])],[(0,[z0,z89,z2,z507,z4,z6]),(0,[z0,z1,z2,z3,z806,z6]),(0,[z1,z857,z2,z3,z4,z6])],[(0,[z0,z378,z2,z3,z5,z6])],[(0,[z118,z1,z2,z296,z4,z6]),(0,[z0,z1,z2,z763,z4,z6])],[(0,[z0,z1,z858,z3,z4,z6]),(0,[z0,z1,z2,z3,z859,z6])],[(0,[z0,z1,z2,z3,z4,z810]),(0,[z0,z2,z3,z4,z860,z6])],[(0,[z24,z1,z2,z678,z3,z4]),(0,[z0,z1,z2,z487,z4,z80])],[(0,[z36,z0,z2,z3,z91,z6]),(0,[z0,z861,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z862,z6]),(0,[z41,z1,z2,z3,z4,z187])],[(0,[z0,z1,z2,z863,z4,z6]),(0,[z0,z1,z2,z767,z4,z6]),(0,[z0,z864,z2,z3,z4,z6]),(0,[z0,z2,z301,z3,z5,z6])],[],[],[(0,[z0,z1,z2,z3,z4,z865])],[(0,[z0,z2,z3,z4,z866,z6]),(0,[z0,z2,z3,z5,z285,z6]),(0,[z2,z3,z4,z5,z6,z517])],[(0,[z0,z1,z2,z3,z867,z6])],[(0,[z0,z1,z868,z3,z4,z6])],[(0,[z118,z1,z2,z678,z4,z6])]]

def bk1_12 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z756,z4,z6])],[(0,[z0,z12,z2,z3,z5,z6]),(0,[z0,z9,z2,z3,z4,z54])],[(0,[z175,z318,z2,z3,z4,z6])],[(0,[z118,z1,z2,z38,z4,z6])],[(0,[z0,z869,z2,z3,z4,z6]),(0,[z0,z2,z3,z397,z5,z6])],[(0,[z0,z2,z870,z3,z4,z6]),(0,[z0,z2,z3,z5,z6,z293])],[(0,[z0,z174,z235,z3,z4,z6])],[(0,[z0,z124,z2,z3,z125,z159]),(0,[z0,z78,z2,z29,z3,z6])],[(0,[z0,z12,z235,z3,z4,z6])],[(0,[z871,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z872,z4,z6]),(0,[z0,z78,z2,z3,z116,z6])],[(0,[z0,z814,z2,z3,z22,z6]),(0,[z0,z873,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z84,z187]),(0,[z0,z2,z3,z4,z874,z6])],[],[(0,[z0,z1,z2,z3,z4,z875]),(0,[z0,z1,z2,z3,z4,z876]),(0,[z0,z2,z3,z84,z5,z6]),(0,[z0,z2,z3,z4,z5,z6])],[(0,[z268,z1,z2,z3,z4,z50]),(0,[z877,z2,z3,z4,z5,z6])],[(0,[z878,z1,z2,z3,z4,z6])]]

def bk1_13 : List (List (ℕ × List W)) :=
  [[(0,[z85,z857,z2,z3,z4,z6])],[],[],[(0,[z0,z2,z29,z3,z5,z6]),(0,[z0,z2,z3,z4,z879,z6])],[],[],[(0,[z880,z1,z2,z3,z4,z6])],[(0,[z0,z2,z348,z4,z5,z6])],[(0,[z0,z881,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z882])],[(0,[z0,z130,z2,z37,z4,z6]),(0,[z0,z2,z3,z116,z5,z69])],[],[(0,[z0,z883,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z91,z187]),(0,[z0,z2,z3,z742,z4,z6])],[(0,[z406,z1,z2,z355,z4,z6])],[(0,[z406,z1,z2,z3,z4,z358])],[(0,[z0,z1,z2,z884,z3,z4]),(0,[z0,z1,z2,z3,z4,z885])],[]]

def bk1_14 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z3,z4,z886]),(0,[z0,z130,z2,z3,z156,z6]),(0,[z1,z2,z3,z4,z789,z50])],[],[(0,[z0,z1,z2,z3,z4,z882]),(0,[z0,z1,z2,z3,z4,z887])],[(0,[z0,z1,z2,z3,z888,z6]),(0,[z0,z1,z2,z3,z889,z6])],[(0,[z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z890,z6])],[],[(0,[z0,z17,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z891,z6]),(0,[z0,z1,z2,z3,z346,z6]),(0,[z0,z2,z3,z631,z5,z6])],[(0,[z0,z1,z2,z309,z4,z50]),(0,[z0,z2,z3,z457,z5,z6])],[(0,[z0,z68,z2,z29,z3,z5]),(0,[z0,z1,z892,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z54])],[(0,[z0,z174,z893,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z894])],[(0,[z0,z338,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z633,z6]),(0,[z0,z857,z2,z3,z4,z6])],[],[(0,[z36,z41,z2,z3,z4,z6]),(0,[z24,z1,z2,z348,z4,z50])],[(0,[z895,z0,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z142])]]

def bk1_15 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z4,z896])],[(0,[z0,z9,z2,z3,z524,z6])],[(0,[z24,z1,z2,z3,z4,z50]),(0,[z0,z2,z3,z897,z4,z6])],[(0,[z24,z1,z59,z2,z102,z4]),(0,[z898,z1,z2,z3,z4,z6]),(0,[z0,z124,z2,z3,z4,z132]),(0,[z0,z1,z2,z899,z4,z6])],[(0,[z0,z2,z377,z3,z5,z6])],[(0,[z0,z1,z2,z900,z4,z6])],[(0,[z0,z89,z2,z3,z33,z6]),(0,[z0,z1,z2,z901,z4,z6]),(0,[z0,z2,z60,z3,z5,z6]),(0,[z175,z1,z2,z37,z4,z6])],[(0,[z0,z902,z2,z3,z4,z6]),(0,[z0,z1,z2,z903,z4,z6])],[(0,[z0,z1,z2,z3,z904,z6]),(0,[z0,z905,z2,z3,z4,z6]),(0,[z41,z1,z2,z355,z4,z6])],[(0,[z0,z1,z2,z355,z4,z358]),(0,[z0,z2,z271,z4,z5,z6])],[(0,[z0,z1,z2,z3,z846,z6]),(0,[z0,z2,z16,z3,z806,z6]),(0,[z1,z2,z3,z4,z25,z550])],[(0,[z0,z1,z2,z3,z4,z906]),(0,[z0,z1,z2,z907,z4,z6])],[(0,[z72,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z479,z5,z6])],[(0,[z0,z1,z2,z309,z4,z25])],[],[(0,[z0,z908,z2,z3,z4,z6]),(0,[z0,z909,z2,z3,z4,z6])]]

def bk1_16 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z910,z4,z6]),(0,[z0,z2,z117,z746,z4,z6])],[(0,[z506,z42,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z911,z6]),(0,[z0,z78,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z912,z6])],[(0,[z0,z1,z913,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z914]),(0,[z0,z2,z893,z3,z4,z6])],[(0,[z915,z1,z2,z3,z4,z6]),(0,[z0,z9,z2,z79,z4,z80]),(0,[z0,z1,z2,z3,z916,z6]),(0,[z0,z2,z3,z5,z373,z6])],[(0,[z0,z9,z2,z3,z256,z6]),(0,[z0,z1,z2,z3,z917,z6])],[(0,[z0,z1,z2,z918,z4,z6]),(0,[z0,z1,z2,z919,z4,z6])],[(0,[z175,z9,z2,z3,z4,z6])],[(0,[z0,z2,z3,z398,z5,z6])],[(0,[z0,z920,z2,z3,z4,z6]),(0,[z0,z2,z402,z3,z5,z6])],[(0,[z0,z2,z3,z5,z380,z6])],[(0,[z109,z857,z2,z3,z4,z6]),(0,[z0,z921,z2,z3,z4,z6])],[(0,[z0,z575,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z4,z838]),(0,[z0,z2,z3,z4,z922,z6])],[],[(0,[z118,z1,z2,z38,z4,z142]),(0,[z0,z332,z2,z3,z5,z6])],[(0,[z0,z9,z2,z3,z4,z187]),(0,[z0,z1,z2,z79,z4,z550]),(0,[z2,z3,z23,z192,z5,z6])]]

def bk1_17 : List (List (ℕ × List W)) :=
  [[],[(0,[z101,z0,z1,z2,z296,z4]),(0,[z0,z1,z2,z923,z4,z6]),(0,[z0,z2,z411,z3,z5,z6])],[(0,[z0,z760,z2,z3,z116,z6]),(0,[z0,z1,z2,z3,z924,z6])],[(0,[z0,z2,z21,z60,z5,z6])],[],[(0,[z72,z1,z2,z3,z4,z45])],[(0,[z0,z1,z2,z348,z4,z6]),(0,[z0,z1,z2,z348,z4,z80]),(0,[z925,z1,z2,z3,z4,z6])],[(0,[z1,z2,z751,z3,z4,z6])],[(0,[z0,z926,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z142]),(0,[z1,z2,z927,z3,z4,z6])],[(0,[z72,z1,z2,z3,z4,z54])],[(0,[z88,z2,z3,z22,z5,z6]),(0,[z0,z1,z2,z3,z928,z6]),(0,[z0,z1,z2,z3,z4,z6])],[(0,[z877,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z929,z6])],[(0,[z0,z76,z2,z3,z4,z6]),(0,[z0,z930,z2,z3,z4,z6])],[(0,[z0,z32,z2,z117,z7,z6]),(0,[z0,z931,z2,z3,z4,z6]),(0,[z0,z2,z932,z4,z5,z6]),(0,[z933,z1,z2,z3,z4,z6])],[(0,[z268,z1,z2,z4,z112,z6]),(0,[z0,z1,z2,z3,z934,z6]),(0,[z0,z1,z2,z3,z935,z6])],[]]

def bk1_18 : List (List (ℕ × List W)) :=
  [[],[],[(0,[z0,z9,z2,z296,z3,z4]),(0,[z936,z1,z2,z3,z4,z6])],[(0,[z937,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z938,z6])],[(0,[z0,z174,z2,z3,z91,z6])],[(0,[z62,z0,z130,z3,z156,z6]),(0,[z268,z1,z2,z3,z4,z25]),(0,[z0,z939,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z940,z6])],[(0,[z0,z12,z2,z3,z91,z6]),(0,[z0,z2,z3,z4,z941,z6])],[(0,[z9,z2,z3,z4,z6,z517])],[],[(0,[z0,z2,z451,z3,z5,z6]),(0,[z0,z2,z3,z734,z4,z6])],[],[],[(0,[z0,z1,z2,z3,z4,z942])],[(0,[z0,z1,z2,z4,z943,z6]),(0,[z0,z2,z3,z4,z944,z6])],[],[(0,[z0,z945,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z946,z6])]]

def bk1_19 : List (List (ℕ × List W)) :=
  [[(0,[z24,z1,z703,z2,z3,z4]),(0,[z175,z2,z3,z4,z5,z6])],[],[(0,[z0,z2,z551,z3,z5,z6])],[(0,[z406,z1,z2,z3,z84,z6]),(0,[z0,z1,z2,z947,z3,z6]),(0,[z0,z2,z466,z3,z5,z6]),(0,[z0,z2,z3,z4,z6,z948])],[(0,[z0,z9,z2,z3,z326,z6]),(0,[z0,z1,z2,z3,z949,z6]),(0,[z0,z1,z2,z3,z950,z6]),(0,[z0,z1,z2,z4,z811,z6])],[(0,[z0,z76,z2,z3,z66,z6]),(0,[z0,z951,z2,z3,z4,z6])],[(0,[z0,z1,z2,z952,z4,z6]),(0,[z0,z2,z561,z3,z5,z6]),(0,[z0,z2,z296,z3,z4,z5])],[(0,[z0,z953,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z54]),(0,[z954,z1,z2,z3,z4,z6])],[(0,[z502,z0,z1,z3,z156,z6]),(0,[z0,z135,z2,z3,z66,z6]),(0,[z0,z2,z3,z4,z5,z187])],[(0,[z830,z1,z2,z3,z4,z6])],[(0,[z0,z955,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z956,z6]),(0,[z0,z2,z3,z4,z957,z6])],[(0,[z24,z1,z2,z3,z4,z550]),(0,[z0,z814,z2,z3,z4,z6]),(0,[z0,z1,z2,z746,z4,z6])],[(0,[z0,z1,z2,z3,z4,z958]),(0,[z0,z2,z3,z566,z5,z6]),(0,[z41,z1,z2,z3,z4,z358])],[(0,[z24,z1,z2,z348,z3,z4])],[(0,[z268,z1,z2,z38,z4,z6]),(0,[z0,z407,z2,z3,z346,z6])],[]]

def bk1_20 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z959,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z789]),(0,[z0,z1,z2,z3,z960,z6])],[(0,[z0,z32,z2,z402,z4,z6]),(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z1,z2,z3,z4,z962]),(0,[z0,z3,z181,z5,z156,z6])],[],[(0,[z62,z0,z1,z134,z156,z6]),(0,[z963,z0,z2,z3,z4,z6]),(0,[z406,z1,z2,z3,z91,z6]),(0,[z0,z964,z2,z3,z4,z6])],[(0,[z0,z2,z488,z3,z5,z6]),(0,[z965,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z966,z4,z6]),(0,[z0,z114,z2,z3,z346,z6]),(0,[z0,z2,z3,z490,z5,z6])],[],[(0,[z967,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z968,z4,z6])],[(0,[z0,z969,z2,z3,z4,z6]),(0,[z0,z760,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z787])],[],[(0,[z0,z2,z970,z4,z5,z6])],[(0,[z0,z1,z2,z79,z309,z4]),(0,[z0,z1,z2,z971,z4,z6])],[(0,[z118,z1,z195,z2,z38,z4]),(0,[z0,z1,z2,z271,z4,z187]),(0,[z0,z83,z639,z3,z4,z6]),(0,[z0,z2,z3,z5,z473,z6])],[(0,[z0,z1,z2,z3,z972,z6]),(0,[z0,z2,z201,z3,z4,z6]),(0,[z0,z2,z134,z4,z5,z6])],[(0,[z268,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z973,z6]),(0,[z0,z1,z2,z355,z84,z6]),(0,[z41,z1,z2,z3,z84,z6])]]

def bk1_21 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z3,z84,z358]),(0,[z0,z974,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z975]),(0,[z976,z1,z2,z3,z4,z6])],[],[(0,[z0,z32,z2,z117,z4,z6]),(0,[z175,z1,z2,z3,z4,z45])],[(0,[z0,z63,z3,z169,z5,z6]),(0,[z0,z2,z3,z511,z5,z6]),(0,[z0,z2,z3,z4,z977,z6])],[],[],[(0,[z978,z1,z2,z3,z4,z6])],[(0,[z0,z1,z59,z2,z309,z4])],[(0,[z0,z1,z2,z3,z4,z979])],[(0,[z268,z1,z2,z3,z4,z550])],[(0,[z347,z85,z2,z3,z4,z6]),(0,[z0,z154,z2,z3,z4,z147]),(0,[z0,z1,z2,z3,z980,z6])],[(0,[z0,z981,z2,z3,z4,z6])],[(0,[z0,z982,z2,z3,z4,z6]),(0,[z0,z2,z60,z19,z5,z6])],[],[(0,[z62,z0,z9,z3,z156,z6]),(0,[z0,z1,z2,z355,z91,z6]),(0,[z0,z1,z2,z4,z983,z6]),(0,[z41,z1,z2,z3,z91,z6])]]

def bk1_22 : List (List (ℕ × List W)) :=
  [[(0,[z0,z984,z2,z3,z4,z6]),(0,[z0,z318,z2,z134,z4,z6]),(0,[z0,z1,z2,z3,z91,z358]),(0,[z0,z130,z2,z3,z4,z6])],[(0,[z0,z2,z3,z608,z5,z6])],[(0,[z0,z9,z2,z134,z4,z6]),(0,[z0,z792,z2,z3,z4,z6]),(0,[z0,z135,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z985]),(0,[z0,z2,z986,z3,z4,z6])],[(0,[z0,z9,z2,z738,z4,z6])],[(0,[z0,z1,z2,z3,z4,z142]),(0,[z0,z2,z3,z5,z504,z6])],[(0,[z0,z1,z2,z3,z987,z6]),(0,[z0,z556,z2,z3,z23,z6])],[(0,[z0,z9,z2,z3,z33,z6])],[(0,[z0,z1,z2,z3,z4,z988]),(0,[z0,z2,z3,z534,z5,z6]),(0,[z0,z2,z3,z5,z512,z6])],[],[(0,[z0,z9,z2,z309,z4,z6])],[(0,[z0,z989,z2,z3,z4,z6]),(0,[z0,z1,z2,z990,z4,z6])],[],[],[(0,[z0,z991,z2,z3,z4,z6])],[(0,[z0,z992,z2,z3,z4,z6]),(0,[z0,z2,z3,z541,z5,z6])]]

def bk1_23 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z4,z993,z6])],[(0,[z502,z0,z3,z5,z156,z6]),(0,[z0,z1,z2,z3,z994,z6]),(0,[z0,z1,z995,z3,z4,z6])],[(0,[z0,z1,z2,z996,z4,z6])],[(0,[z0,z9,z2,z3,z4,z997]),(0,[z0,z2,z3,z4,z806,z6]),(0,[z0,z2,z3,z5,z526,z6])],[(0,[z0,z1,z2,z3,z998,z6])],[(0,[z0,z1,z2,z4,z999,z6])],[(0,[z0,z588,z2,z3,z5,z6]),(0,[z1000,z9,z2,z3,z4,z6])],[(0,[z406,z9,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1001,z6])],[(0,[z268,z2,z3,z4,z5,z6]),(0,[z1002,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1003,z4,z6])],[(0,[z0,z130,z2,z3,z4,z45]),(0,[z0,z2,z3,z4,z241,z6]),(0,[z0,z3,z169,z5,z156,z6])],[(0,[z371,z114,z2,z3,z4,z6]),(0,[z0,z1,z2,z79,z4,z80]),(0,[z0,z1004,z2,z3,z4,z6]),(0,[z0,z2,z60,z56,z5,z6])],[(0,[z0,z1,z2,z3,z256,z6]),(0,[z0,z1005,z2,z3,z4,z6])],[(0,[z0,z1,z2,z947,z3,z4]),(0,[z0,z1,z2,z3,z1006,z6]),(0,[z0,z1,z2,z3,z1007,z6])],[(0,[z0,z130,z2,z3,z4,z54]),(0,[z0,z2,z3,z587,z5,z6]),(0,[z175,z1,z2,z3,z4,z6])],[(0,[z0,z9,z2,z3,z125,z6]),(0,[z0,z2,z409,z188,z4,z6])],[(0,[z0,z1008,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1009])]]

def bk1_24 : List (List (ℕ × List W)) :=
  [[(0,[z109,z0,z2,z3,z91,z6]),(0,[z0,z261,z2,z3,z4,z6]),(0,[z0,z1,z2,z348,z4,z112])],[(0,[z0,z1,z2,z1010,z4,z6])],[(0,[z0,z1011,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1012,z6])],[(0,[z0,z1013,z2,z3,z4,z6])],[(0,[z0,z2,z572,z3,z5,z6])],[(0,[z72,z130,z2,z3,z4,z6]),(0,[z0,z55,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z4,z187]),(0,[z0,z1,z1014,z3,z4,z6]),(0,[z0,z2,z29,z3,z5,z75])],[(0,[z1015,z0,z2,z3,z4,z6]),(0,[z0,z386,z2,z3,z5,z6]),(0,[z0,z2,z3,z635,z5,z6])],[(0,[z0,z1,z2,z1016,z4,z6])],[(0,[z0,z1,z1017,z2,z3,z4]),(0,[z0,z2,z3,z249,z4,z155]),(0,[z0,z2,z3,z4,z178,z6])],[(0,[z0,z1,z2,z3,z1018,z6]),(0,[z0,z2,z3,z5,z6,z553])],[(0,[z0,z2,z640,z3,z5,z6]),(0,[z0,z2,z3,z4,z1019,z6])],[(0,[z0,z55,z2,z60,z5,z6]),(0,[z0,z2,z3,z643,z5,z6]),(0,[z0,z2,z3,z5,z559,z6])],[(0,[z0,z42,z2,z3,z5,z6])],[(0,[z0,z2,z746,z3,z4,z6])],[(0,[z0,z1020,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1021,z6]),(0,[z0,z2,z3,z33,z5,z6])],[(0,[z0,z2,z3,z651,z5,z6]),(0,[z0,z2,z3,z4,z1022,z6]),(1,[z24,z1,z2,z348,z4])]]

def bk1_25 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1023,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1024,z6])],[],[(0,[z0,z9,z2,z355,z4,z6]),(0,[z0,z1,z2,z1025,z4,z6]),(0,[z0,z2,z3,z4,z1026,z6]),(0,[z41,z9,z2,z3,z4,z6])],[(0,[z0,z9,z2,z3,z4,z358]),(0,[z1,z2,z3,z4,z789,z6])],[(0,[z0,z9,z2,z3,z5,z6])],[(0,[z62,z175,z1,z3,z156,z6]),(0,[z0,z1,z2,z970,z4,z6]),(0,[z0,z2,z3,z633,z5,z6])],[],[(0,[z0,z1,z2,z296,z3,z4])],[],[(0,[z0,z154,z2,z3,z256,z6]),(0,[z175,z1,z2,z3,z4,z54]),(0,[z1,z2,z3,z4,z6,z1027])],[(0,[z0,z1,z59,z2,z296,z4]),(0,[z0,z1,z2,z3,z1028,z6])],[],[(0,[z0,z1,z2,z1029,z4,z6])],[(0,[z0,z1030,z2,z3,z4,z6])],[]]

def bk1_26 : List (List (ℕ × List W)) :=
  [[(0,[z406,z2,z3,z4,z5,z6]),(0,[z0,z9,z2,z3,z514,z6])],[(0,[z0,z1,z2,z1031,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1032]),(0,[z0,z2,z117,z3,z33,z6])],[(0,[z0,z176,z2,z3,z4,z147]),(0,[z0,z2,z3,z676,z5,z6])],[(0,[z0,z2,z46,z3,z91,z6]),(0,[z0,z2,z3,z4,z287,z6]),(0,[z0,z2,z3,z5,z132,z6])],[(0,[z0,z1033,z2,z3,z4,z6])],[],[],[(0,[z268,z1,z2,z102,z4,z6]),(0,[z0,z2,z1034,z3,z4,z6])],[],[],[],[(0,[z0,z2,z3,z443,z5,z6])],[(0,[z40,z0,z2,z3,z346,z6]),(0,[z0,z1,z2,z1035,z4,z6])],[(0,[z0,z9,z2,z3,z742,z6]),(0,[z0,z1,z2,z1036,z4,z6]),(0,[z0,z2,z4,z5,z494,z6])],[(0,[z0,z195,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z6,z1037])]]

def bk1_27 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z1038,z3,z4,z6]),(0,[z0,z1,z2,z3,z1039,z6]),(0,[z0,z2,z3,z256,z5,z6])],[(0,[z0,z1040,z2,z3,z4,z6])],[(0,[z1,z2,z348,z4,z25,z6])],[(0,[z0,z1041,z2,z3,z4,z6])],[(0,[z0,z1042,z2,z3,z4,z6]),(0,[z0,z1,z2,z932,z4,z6])],[(0,[z406,z1,z2,z271,z4,z6])],[(0,[z0,z1,z2,z3,z765,z6])],[(0,[z109,z41,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z91,z6]),(0,[z0,z83,z893,z3,z4,z6])],[(0,[z64,z0,z2,z402,z4,z6]),(0,[z24,z1,z2,z309,z4,z50])],[],[(0,[z1,z2,z296,z102,z3,z4])],[(0,[z62,z0,z1,z37,z156,z6])],[],[(0,[z0,z1,z2,z3,z1043,z6]),(0,[z0,z2,z3,z4,z5,z358])],[(0,[z1,z2,z892,z3,z4,z6])],[(0,[z0,z9,z2,z3,z4,z752]),(0,[z0,z9,z2,z4,z494,z6]),(0,[z0,z629,z2,z3,z5,z6])]]

def bk1_28 : List (List (ℕ × List W)) :=
  [[(0,[z118,z1,z2,z4,z112,z25]),(0,[z268,z1,z2,z79,z3,z4]),(0,[z0,z130,z2,z3,z169,z6])],[],[(0,[z0,z792,z2,z3,z169,z6]),(0,[z0,z1,z2,z3,z1044,z6])],[(0,[z0,z1045,z2,z3,z4,z6]),(0,[z175,z130,z2,z3,z4,z6])],[(0,[z486,z0,z2,z3,z779,z6]),(0,[z0,z1,z2,z3,z1046,z6]),(1,[z268,z1,z2,z79,z4])],[(0,[z268,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z112,z550])],[],[(0,[z0,z9,z2,z3,z689,z6]),(0,[z0,z1047,z2,z3,z4,z6]),(0,[z0,z2,z3,z23,z5,z6])],[],[(0,[z0,z1048,z2,z3,z4,z6])],[(0,[z371,z2,z3,z23,z5,z6]),(0,[z0,z1,z851,z2,z4,z6]),(0,[z0,z2,z3,z4,z1049,z6])],[(0,[z371,z2,z3,z4,z480,z6]),(0,[z0,z124,z2,z3,z4,z743])],[(0,[z268,z1,z59,z2,z3,z4]),(0,[z0,z1050,z1,z2,z3,z6]),(0,[z1051,z1,z2,z3,z4,z6])],[(0,[z0,z338,z2,z3,z633,z6]),(0,[z0,z2,z641,z3,z5,z6])],[(0,[z1052,z1,z2,z3,z4,z6]),(0,[z1053,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z722,z6])]]

def bk1_29 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1054,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z1055,z6]),(0,[z41,z1,z2,z271,z4,z6])],[(0,[z0,z1,z2,z271,z4,z358]),(0,[z0,z1,z2,z3,z4,z1056])],[(0,[z0,z2,z652,z3,z5,z6])],[],[],[],[],[(0,[z0,z9,z2,z3,z4,z783]),(0,[z0,z318,z2,z37,z4,z6]),(0,[z0,z1,z2,z134,z4,z6])],[],[(0,[z24,z118,z1,z2,z79,z4])],[(0,[z1057,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1058,z4,z6])],[(0,[z0,z1,z2,z1059,z4,z6])],[(0,[z486,z41,z2,z3,z4,z6]),(0,[z0,z1,z2,z1060,z4,z6]),(0,[z0,z1,z2,z3,z33,z6])],[(0,[z0,z9,z2,z795,z4,z6]),(0,[z0,z1061,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z747])],[(0,[z0,z9,z2,z3,z4,z796]),(0,[z1062,z1,z2,z3,z4,z6])]]

def bk1_30 : List (List (ℕ × List W)) :=
  [[(0,[z0,z9,z2,z462,z4,z6]),(0,[z0,z1063,z2,z3,z4,z6]),(0,[z0,z1,z2,z309,z4,z6]),(0,[z0,z2,z3,z704,z5,z6])],[(0,[z0,z2,z117,z188,z4,z6])],[(0,[z0,z176,z2,z3,z256,z6])],[],[(0,[z0,z1,z2,z79,z4,z961]),(0,[z0,z1064,z2,z3,z4,z6]),(0,[z0,z2,z29,z3,z116,z5])],[(0,[z24,z1,z2,z348,z4,z6]),(0,[z0,z9,z195,z2,z3,z4]),(0,[z0,z1065,z2,z3,z4,z6]),(0,[z0,z1,z2,z38,z4,z550])],[],[(0,[z0,z2,z3,z111,z5,z6])],[(0,[z0,z675,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z4,z997])],[(0,[z0,z9,z2,z3,z84,z6]),(0,[z0,z1066,z2,z3,z4,z6]),(0,[z0,z556,z2,z3,z22,z6])],[(0,[z0,z1067,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1068,z4,z6]),(0,[z1000,z1,z2,z3,z4,z6])],[(0,[z406,z1,z2,z3,z4,z6]),(0,[z0,z124,z2,z3,z4,z159]),(0,[z0,z1069,z2,z3,z4,z6]),(0,[z0,z1,z2,z1070,z4,z6]),(0,[z0,z1,z2,z4,z961,z6]),(0,[z0,z1,z2,z4,z961,z80])],[],[]]

def bk1_31 : List (List (ℕ × List W)) :=
  [[(0,[z0,z799,z2,z3,z4,z5])],[(0,[z36,z42,z2,z3,z4,z6]),(0,[z0,z1,z2,z134,z4,z45]),(0,[z0,z1071,z2,z3,z4,z6])],[(0,[z0,z492,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z4,z1072]),(0,[z0,z2,z462,z4,z5,z6])],[(0,[z0,z379,z2,z4,z6,z533])],[(0,[z0,z1,z2,z3,z125,z6]),(0,[z0,z1,z2,z4,z1073,z6]),(0,[z0,z1,z893,z3,z4,z6]),(0,[z0,z2,z60,z3,z178,z6]),(0,[z0,z2,z3,z91,z5,z6])],[(0,[z109,z2,z324,z3,z4,z6]),(0,[z0,z1,z2,z134,z4,z54]),(0,[z0,z1,z2,z271,z91,z6])],[(0,[z0,z9,z2,z3,z4,z550])],[(0,[z0,z379,z2,z61,z4,z6]),(0,[z0,z2,z3,z4,z6,z743]),(0,[z0,z2,z3,z5,z673,z6])],[(0,[z0,z1,z2,z1074,z4,z6])],[],[(0,[z0,z2,z137,z3,z5,z6])],[(0,[z0,z338,z2,z3,z4,z6]),(0,[z0,z1,z1075,z2,z4,z6])],[(0,[z118,z0,z1,z2,z296,z4]),(0,[z0,z1076,z2,z3,z4,z6])],[(0,[z268,z0,z1,z2,z79,z4]),(0,[z72,z1,z2,z134,z4,z6])],[(0,[z0,z2,z3,z144,z5,z6])],[(0,[z62,z0,z318,z3,z156,z6]),(0,[z0,z1,z3,z846,z156,z6]),(0,[z41,z2,z3,z4,z5,z6])]]

def bk1 : List (List (List (ℕ × List W))) :=
  [bk1_0, bk1_1, bk1_2, bk1_3, bk1_4, bk1_5, bk1_6, bk1_7, bk1_8, bk1_9, bk1_10, bk1_11, bk1_12, bk1_13, bk1_14, bk1_15, bk1_16, bk1_17, bk1_18, bk1_19, bk1_20, bk1_21, bk1_22, bk1_23, bk1_24, bk1_25, bk1_26, bk1_27, bk1_28, bk1_29, bk1_30, bk1_31]

def bk2_0 : List (List (ℕ × List W)) :=
  [[(0,[z268,z1,z2,z1077,z4])],[(0,[z24,z9,z2,z348,z4]),(0,[z24,z1,z2,z1077,z4])],[(0,[z0,z2,z3,z5,z894]),(0,[z0,z2,z3,z5,z727]),(0,[z1,z2,z4,z943,z25]),(0,[z2,z3,z4,z1078,z6])],[(0,[z1,z1017,z2,z102,z4]),(0,[z2,z3,z765,z5,z6])]]

def bk2_1 : List (List (ℕ × List W)) :=
  [[(0,[z118,z1,z2,z1077,z4]),(0,[z0,z2,z1079,z3,z4]),(0,[z0,z2,z3,z125,z743])],[(0,[z268,z1,z2,z678,z4])],[(0,[z268,z1,z2,z348,z4]),(0,[z0,z2,z5,z6,z804])],[(0,[z24,z1,z2,z348,z4]),(0,[z118,z1,z2,z1080,z4]),(0,[z0,z792,z3,z156,z6]),(0,[z0,z130,z3,z846,z6]),(0,[z41,z2,z3,z806,z6])]]

def bk2_2 : List (List (ℕ × List W)) :=
  [[(0,[z0,z2,z3,z1081,z6])],[(0,[z268,z1,z2,z487,z4]),(0,[z0,z2,z3,z1082,z6]),(0,[z976,z2,z3,z5,z6])],[(0,[z0,z2,z3,z1083,z6]),(0,[z0,z2,z4,z6,z1084])],[(0,[z0,z1,z2,z1077,z4]),(0,[z0,z2,z3,z5,z975])]]

def bk2_3 : List (List (ℕ × List W)) :=
  [[],[],[(0,[z24,z2,z348,z4,z5]),(0,[z0,z2,z746,z7,z6]),(0,[z0,z2,z795,z5,z6])],[(0,[z0,z2,z3,z5,z752])]]

def bk2_4 : List (List (ℕ × List W)) :=
  [[],[(0,[z268,z2,z79,z4,z5]),(0,[z175,z1,z37,z156,z6])],[(0,[z0,z731,z2,z5,z6]),(0,[z0,z2,z707,z5,z6])],[(0,[z0,z2,z3,z256,z132])]]

def bk2_5 : List (List (ℕ × List W)) :=
  [[(0,[z24,z1,z2,z1085,z4]),(0,[z0,z2,z3,z4,z1086])],[(0,[z0,z1075,z2,z5,z6]),(0,[z0,z2,z947,z3,z5]),(0,[z0,z868,z3,z5,z6]),(0,[z175,z1,z3,z156,z54])],[(0,[z268,z9,z2,z79,z4]),(0,[z268,z1,z2,z296,z4])],[(0,[z118,z9,z2,z296,z4])]]

def bk2_6 : List (List (ℕ × List W)) :=
  [[],[],[(0,[z118,z1,z2,z296,z4]),(0,[z0,z1,z37,z156,z54]),(0,[z0,z2,z3,z806,z6]),(0,[z0,z3,z5,z846,z6])],[(0,[z0,z2,z1087,z4,z6]),(0,[z41,z2,z3,z346,z6])]]

def bk2_7 : List (List (ℕ × List W)) :=
  [[(0,[z268,z1,z2,z79,z4]),(0,[z1088,z2,z3,z4,z6])],[(0,[z0,z2,z402,z33,z6])],[(0,[z118,z2,z296,z4,z5]),(0,[z42,z2,z3,z346,z6])],[]]

def bk2 : List (List (List (ℕ × List W))) :=
  [bk2_0, bk2_1, bk2_2, bk2_3, bk2_4, bk2_5, bk2_6, bk2_7]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fin0 : chunkOK 4 ((bk2.flatten.drop 0).take 32).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem finend : (bk2.flatten.drop 32).isEmpty = true := by
  decide +kernel

theorem winF : windowsF 4 bk2.flatten 0 [32] = true :=
  windowsF_cons fin0 (windowsF_nil finend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t1w0 : chunkB (fun c => !inB2 4 32 bk2 c) 1 ((bk1.flatten.flatten.drop 0).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t1w1 : chunkB (fun c => !inB2 4 32 bk2 c) 1 ((bk1.flatten.flatten.drop 400).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t1w2 : chunkB (fun c => !inB2 4 32 bk2 c) 1 ((bk1.flatten.flatten.drop 800).take 101) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t1wend : (bk1.flatten.flatten.drop 901).isEmpty = true := by
  decide +kernel

theorem win1 : windowsG (chunkB (fun c => !inB2 4 32 bk2 c) 1) bk1.flatten.flatten 0 [400, 400, 101] = true :=
  windowsG_cons t1w0 (windowsG_cons t1w1 (windowsG_cons t1w2 (windowsG_nil t1wend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t0w0 : chunkB (fun c => !inB2 16 512 bk1 c) 1 ((bk0.flatten.flatten.drop 0).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t0w1 : chunkB (fun c => !inB2 16 512 bk1 c) 1 ((bk0.flatten.flatten.drop 400).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t0w2 : chunkB (fun c => !inB2 16 512 bk1 c) 1 ((bk0.flatten.flatten.drop 800).take 359) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem t0wend : (bk0.flatten.flatten.drop 1159).isEmpty = true := by
  decide +kernel

theorem win0 : windowsG (chunkB (fun c => !inB2 16 512 bk1 c) 1) bk0.flatten.flatten 0 [400, 400, 359] = true :=
  windowsG_cons t0w0 (windowsG_cons t0w1 (windowsG_cons t0w2 (windowsG_nil t0wend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pw0 : chunkB (fun c => !inB2 16 512 bk0 c) 2 (((level0 8 rows).drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pwend : ((level0 8 rows).drop 1).isEmpty = true := by
  decide +kernel

theorem winP : windowsG (chunkB (fun c => !inB2 16 512 bk0 c) 2) (level0 8 rows) 0 [1] = true :=
  windowsG_cons pw0 (windowsG_nil pwend)

theorem reject : search 8 rows = false := by
  have h2 : FalseAt 4 bk2.flatten.flatten := finalF winF
  have h1 : FalseAt 5 bk1.flatten.flatten := tierB (by norm_num) (memS h2) win1
  have h0 : FalseAt 6 bk0.flatten.flatten := tierB (by norm_num) (memS h1) win0
  have hP : FalseAt 8 (level0 8 rows) := tierB (by norm_num) (memS h0) winP
  exact search_of_false hP

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

end PEqualNP.Outside.L_meta_43890

theorem PEqualNP.Outside.L_meta_43890 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276791424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276791424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43890.solve
