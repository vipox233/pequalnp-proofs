import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36254

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
  Nat.testBit (4277074666 * 2 ^ 32 + 4276681416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x150002012046a18a#64 ++ 0x02a000402408d431#64 ++ 0xfec14633e0cfa79f#64 ++ 0xbfd828c67c19f4f3#64 : BitVec 256),
   (0x0a02192483114434#64 ++ 0x2140432490622886#64 ++ 0xbda6b92c8731c4ff#64 ++ 0x77b4d72590e6389f#64 : BitVec 256),
   (0xa408c04b082a28c0#64 ++ 0x9481180961054518#64 ++ 0xebd8c1cf183e78e6#64 ++ 0xfd7b1839e307cf1c#64 : BitVec 256),
   (0x081701b015805600#64 ++ 0x2102e03602b00ac0#64 ++ 0x67ff01f01fc07f05#64 ++ 0xecffe03e03f80fe0#64 : BitVec 256),
   (0x303dee001efd8000#64 ++ 0xc607bdc003dfb000#64 ++ 0x1fbffe001fff8003#64 ++ 0xe3f7ffc003fff000#64 : BitVec 256),
   (0xc01ff5fec0000000#64 ++ 0xf803febfd8000000#64 ++ 0xff9fffffe0000000#64 ++ 0x1ff3fffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [6, 4]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff01f01fc07f05 0xecffe03e03f80fe0

def z1 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbda6b92c8731c4ff 0x77b4d72590e6389f

def z2 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfec14633e0cfa79f 0xbfd828c67c19f4f3

def z3 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe001fff8003 0xe3f7ffc003fff000

def z4 : W := mkw 0x3d3fefb13ffff78a 0xe7a7fdf627fffef1 0xfffffff3ffffff9f 0xfffffffe7ffffff3

def z5 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd8c1cf183e78e6 0xfd7b1839e307cf1c

def z6 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z7 : W := mkw 0x0a02112481004434 0x2140422490200886 0xa5a6012c870044fd 0x74b4c02590e0089f

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc8000208001849f 0x3790000410003093

def z9 : W := mkw 0x0a02192483114434 0x2140432490622886 0x0126b90c07304060 0x4024d72180e6080c

def z10 : W := mkw 0x0a00080003114434 0x0140010000622886 0x002000000731c4ff 0x6004000000e6389f

def z11 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0x421946d360000000 0x084328da6c000000

def z12 : W := mkw 0x8408c04b00022080 0x9081180960004410 0xebd8c1cf000e2086 0xbd7b1839e001c410

def z13 : W := mkw 0x30200a001efd8000 0x0604014003dfb000 0x002000001fff8003 0xe004000003fff000

def z14 : W := mkw 0xc00211fec0000000 0x3800423fd8000000 0xe00001ffe0000000 0x1c00003ffc000000

def z15 : W := mkw 0x2e0219258b3b6cf4 0x25c04324b1676d9e 0xbde6b92c9f3ffcff 0xf7bcd72593e7ff9f

def z16 : W := mkw 0x0015009014801200 0x0002a01202900240 0x425900d018c03b00 0x884b201a03180760

def z17 : W := mkw 0x0a1719b497915634 0x2142e33692f22ac6 0xffffb9fc9ff1ffff 0xfffff73f93fe3fff

def z18 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xefd9c1ff18fe7fe7 0xfdfb383fe31fcffc

def z19 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x013e01c01f005800 0x4027c03803e00b00

def z20 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x98004603e00f809a 0x130008c07c01f013

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0x63d801c018007804 0xec7b003803000f00

def z22 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdffffff8007804 0xfffbffffff000f00

def z23 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x006000001fc07f05 0xe00c000003f80fe0

def z24 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x8800c00f003e00e2 0x11001801e007c01c

def z25 : W := mkw 0xca1ff5fec1004434 0xf943febfd8200886 0xff9fffffe00044fc 0x1ff3fffffc00089f

def z26 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x14073e30e0000000 0x0280e7c61c000000

def z27 : W := mkw 0xf03ffffedefd8000 0xfe07ffffdbdfb000 0xffbfffffffff8003 0xfff7fffffffff000

def z28 : W := mkw 0x0a02192483114434 0x2140432490622886 0xb800b92c8031c4fe 0x170017259006389f

def z29 : W := mkw 0xc00af5fec0000000 0xf8015ebfd8000000 0xf800ffffe0000000 0x1f001ffffc000000

def z30 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffffffffffc07f05 0xfffffffffff80fe0

def z31 : W := mkw 0xb508c24b286ea9ca 0x96a11849650dd539 0xffd9c7fff8ffffff 0xfffb38ffff1fffff

def z32 : W := mkw 0x0a1711b495805634 0x2142e23692b00ac6 0xe7ff01fc9fc07ffd 0xfcffe03f93f80fff

def z33 : W := mkw 0x2008c8000a390000 0x8401190001472000 0x1fbef8001f3f8003 0xe3f7df0003e7f000

def z34 : W := mkw 0xae0ad96f8b3b6cf4 0xb5c15b2df1676d9e 0xfffef9ef9f3ffcff 0xffffdf3df3e7ff9f

def z35 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x0040000000cfa79f 0xa00800000019f4f3

def z36 : W := mkw 0x3a221b249ffdc434 0x2744436493ffb886 0xbda6b92c9fffc4ff 0xf7b4d72593fff89f

def z37 : W := mkw 0x551737b5e046a18a 0x6aa2e6f6bc08d431 0xfec77e33e0cfa79f 0xbfd8efc67c19f4f3

def z38 : W := mkw 0x24000001082a28c0 0x0480000021054518 0x00000000003e00e2 0x000000000007c01c

def z39 : W := mkw 0x3028ee001efd8000 0xc6051dc003dfb000 0x1820fe001fff8003 0xe3041fc003fff000

def z40 : W := mkw 0x35200a013effa18a 0x06a4014027dff431 0x006000001fffa79f 0xe00c000003fff4f3

def z41 : W := mkw 0x353dee013effa18a 0xc6a7bdc027dff431 0xfffffe33ffffa79f 0xffffffc67ffff4f3

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814633e0000000 0x1fd028c67c000000

def z43 : W := mkw 0xd51ff7ffe046a18a 0xfaa3fefffc08d431 0xffdfffffe0cfa79f 0xbffbfffffc19f4f3

def z44 : W := mkw 0x10352e0016d58000 0x4206a5c002dab000 0x14273e0007c18001 0x0284e7c000f83000

def z45 : W := mkw 0xe408f44fc82a28c0 0xdc811e89f9054518 0x9800fe0fe03e00e2 0x13001fc1fc07c01c

def z46 : W := mkw 0x3028ee000a7d8000 0xc6051dc0014fb000 0x1800fe00003f8002 0x03001fc00007f000

def z47 : W := mkw 0x001701b000000000 0x2002e03600000000 0xff9f47f3e0000000 0x1ff3e8fe7c000000

def z48 : W := mkw 0x383fefb01ffdd600 0xe707fdf603ffbac0 0x7ffffff01fffff07 0xeffffffe03ffffe0

def z49 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffd947f3f8cfff9f 0xfffb28fe7f19fff3

def z50 : W := mkw 0x001de40000000000 0xc003bc8000000000 0xff9ffe33e0000000 0x1ff3ffc67c000000

def z51 : W := mkw 0xf03ffffedefd8000 0xfe07ffffdbdfb000 0x1fbfffcc1fff8003 0xe3f7fff983fff000

def z52 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xeac0400300cfa79f 0xbd5808006019f4f3

def z53 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x013eb8001f300000 0x4027d70003e60000

def z54 : W := mkw 0x1f021b25a357e5be 0x23e04364b46afcb7 0xffe7ff3fe7ffe7ff 0xfffcffe7fcfffcff

def z55 : W := mkw 0x353dee013effa18a 0xc6a7bdc027dff431 0x5ffffe137fffa303 0xebffffc26ffff460

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0xa980810c003040e6 0x753010218006081c

def z57 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x56414633e0cfa719 0x8ac828c67c19f4e3

def z58 : W := mkw 0xca1ffdfec3114434 0xf943ffbfd8622886 0xffbfffffe731c4ff 0x7ff7fffffce6389f

def z59 : W := mkw 0x15021325a046a18a 0x22a04264b408d431 0xffc7ff3fe0cfa79f 0xbff8ffe7fc19f4f3

def z60 : W := mkw 0x0400000100022080 0x0080000020004410 0xeac04003000e2086 0xbd5808006001c410

def z61 : W := mkw 0x191703b035c4d70a 0x2322e07606b89ae1 0x77ff07f0ffc1ff1d 0xeeffe0fe1ff83fe3

def z62 : W := mkw 0x2008c00008280000 0x8401180001050000 0x0b98c000183e0002 0xe17318000307c000

def z63 : W := mkw 0xe01ff5fec8280000 0xfc03febfd9050000 0xff9ffffff83e0002 0xfff3ffffff07c000

def z64 : W := mkw 0xc81ff5fec1004400 0xf903febfd8200880 0xffbfffffe7004405 0x7ff7fffffce00880

def z65 : W := mkw 0xa008c04a08280840 0x9401180941050108 0x011881cc18305860 0x4023103983060b0c

def z66 : W := mkw 0xac1fc1fb1daa7ec0 0xb583f83f63b54fd8 0xefffc1ff1ffe7fe7 0xfdfff83fe3ffcffc

def z67 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x9800fe0fe0000000 0x13001fc1fc000000

def z68 : W := mkw 0x24000001082a28c0 0x0480000021054518 0x00400000183e78e6 0xe00800000307cf1c

def z69 : W := mkw 0x0000000000000000 0x0000000000000000 0xbd80812c8031c4ff 0x77b010259006389f

def z70 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffbfffffff005800 0x5ff7ffffffe00b00

def z71 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xe2414633e0ce279c 0x9c4828c67c19c4f3

def z72 : W := mkw 0x1f021b25a357e5be 0x23e04364b46afcb7 0xfee77e33e7cfa79f 0xbfdcefc67cf9f4f3

def z73 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffbfffffe7c00701 0x1ff7fffffcf800e0

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z75 : W := mkw 0xc50211ffe002218a 0x38a0423ffc004431 0xe04001ffe000279c 0x1c08003ffc0004f3

def z76 : W := mkw 0x8008c04a00000000 0x9001180940000000 0xeb98c1cf00000000 0x1d731839e0000000

def z77 : W := mkw 0xe41ff5ffc82a28c0 0xfc83febff9054518 0xffdffffff83e78e6 0xfffbffffff07cf1c

def z78 : W := mkw 0x3a3fff249ffdc434 0xe747ffe493ffb886 0xbfbfff2c9fffc4ff 0xf7f7ffe593fff89f

def z79 : W := mkw 0xb43dee4b1effa8c0 0xd687bdc963dff518 0xffffffcf1ffff8e7 0xfffffff9e3ffff1c

def z80 : W := mkw 0xaa0ad96e8b394c74 0xb5415b2dd167298e 0x013eb9cc1f305860 0x4027d73983e60b0c

def z81 : W := mkw 0x8008c04a00000000 0x9001180940000000 0x421840c300000000 0x0843081860000000

def z82 : W := mkw 0xa508c04b282a29ca 0x94a1180965054539 0xebd8c1fff83e7ffe 0xfd7b183fff07cfff

def z83 : W := mkw 0x0000000000000000 0x0000000000000000 0x4241001000c02300 0x8848200200180460

def z84 : W := mkw 0xc000104ec0000000 0x18000209d8000000 0x8000000fe0000000 0x10000001fc000000

def z85 : W := mkw 0x0a02192483114434 0x2140432490622886 0xfffeb9ec9f31fcff 0xffffd73d93e63f9f

def z86 : W := mkw 0x8008c04a00000000 0x9001180940000000 0xebd8c1cf18007804 0xfd7b1839e3000f00

def z87 : W := mkw 0x4a173db4c3114434 0x6942e7b698622886 0x14273e30e7018419 0x0284e7c61ce03083

def z88 : W := mkw 0x0a02192483114434 0x2140432490622886 0xffa7ff3fe731c4ff 0x7ff4ffe7fce6389f

def z89 : W := mkw 0x04000001000228c0 0x0080000020004518 0x00400000000078e4 0x0008000000000f1c

def z90 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0x77ff3ff0ffc07f05 0xeeffe7fe1ff80fe0

def z91 : W := mkw 0x0002112480000000 0x2000422490000000 0x0106b90c00000000 0x0020d72180000000

def z92 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x425840c3183e78e6 0xe84b08186307cf1c

def z93 : W := mkw 0xbd1fc3fb3deeffca 0xb7a3f87f67bddff9 0xffffc7ffffffffff 0xfffff8ffffffffff

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0x639801c000000000 0x0c73003800000000

def z95 : W := mkw 0xa81fc1fa1da85e40 0xb503f83f43b50bc8 0x013e81cc1f305860 0x4027d03983e60b0c

def z96 : W := mkw 0xfa3ffffedffdc434 0xff47ffffdbffb886 0xffbfffffffffc4ff 0xfff7fffffffff89f

def z97 : W := mkw 0x0a02112481004434 0x2140422490200886 0xbc80012c8001c4ff 0x379000259000389f

def z98 : W := mkw 0xc01ff5fed4801200 0xf803febfda900240 0xffdffffff8c03b00 0x9ffbffffff180760

def z99 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x604001f000007f04 0x0c08003e00000fe0

def z100 : W := mkw 0xc81ff5fec1005600 0xf903febfd8200ac0 0xffdfffffe0007f04 0x1ffbfffffc000fe0

def z101 : W := mkw 0x0a02112481004434 0x2140422490200886 0xa000012c800044fc 0x140000259000089f

def z102 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xeb98c1cf003e00e2 0x1d731839e007c01c

def z103 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x431fffdf60000000 0x0863fffbec000000

def z104 : W := mkw 0x0a00000001004434 0x0140000000200886 0x00000000000044fc 0x000000000000089f

def z105 : W := mkw 0x0a02192483114434 0x2140432490622886 0x25a6b92c07304465 0x64b4d72580e6088c

def z106 : W := mkw 0x0a0219b483115634 0x2140433690622ac6 0xfde6b9fc8731ffff 0x7fbcd73f90e63fff

def z107 : W := mkw 0xc80211fec1005600 0x3900423fd8200ac0 0xe04001ffe0007f04 0x1c08003ffc000fe0

def z108 : W := mkw 0x0802112481004400 0x2100422490200880 0xbda6b92c87004405 0x77b4d72590e00880

def z109 : W := mkw 0xbe3fff6f9fffecf4 0xf7c7ffedf3fffd9e 0xffffffef9ffffcff 0xfffffffdf3ffff9f

def z110 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x425840c3180e3800 0x884b08186301c700

def z111 : W := mkw 0x0000000000000000 0x0000000000000000 0xa980810c00000000 0x1530102180000000

def z112 : W := mkw 0x30200a001efd8000 0x0604014003dfb000 0x1da6b8001fff8003 0xe3b4d70003fff000

def z113 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0x14273e30e7c00701 0x0284e7c61cf800e0

def z114 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe001849f 0x3ff3fffffc003093

def z115 : W := mkw 0x0a02192483114434 0x2140432490622886 0x0026380007000000 0x0004c70000e00000

def z116 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdfffffe0c02705 0xbffbfffffc1804e0

def z117 : W := mkw 0x2008c00008280000 0x8401180001050000 0x0800c000003e0002 0x010018000007c000

def z118 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x25a7013007c04705 0x64b4e02600f808e0

def z119 : W := mkw 0x303de6001cec8000 0xc607bcc0039d9000 0x0219460018ce0000 0x804328c00319c000

def z120 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x0427003007c00701 0x0084e00600f800e0

def z121 : W := mkw 0x0000000000000000 0x0000000000000000 0x66c1003000c02705 0xacd82006001804e0

def z122 : W := mkw 0xc01711fec0000000 0x3802e23fd8000000 0xe79f01ffe0000000 0x1cf3e03ffc000000

def z123 : W := mkw 0x0200080002110034 0x0040010000422006 0x00000000003180fa 0x000000000006301f

def z124 : W := mkw 0xc00000da40000000 0x1800001b48000000 0x400000d360000000 0x0800001a6c000000

def z125 : W := mkw 0xf03ff7fedcec8000 0xfe07feffdb9d9000 0xff9ffffff8ce0000 0x9ff3ffffff19c000

def z126 : W := mkw 0x0a02192483114434 0x2140432490622886 0xb426392c8701c4fd 0x1684c72590e0389f

def z127 : W := mkw 0x8400004b000228c0 0x1080000960004518 0xe04001cf000078e4 0x1c080039e0000f1c

def z128 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x1f9ffe0000000000 0x03f3ffc000000000

def z129 : W := mkw 0x38370bb01ffdd600 0x2706e17603ffbac0 0x67ff01f01fffff07 0xecffe03e03ffffe0

def z130 : W := mkw 0x201de40008280000 0xc403bc8001050000 0x1f9ffe00183e0002 0xe3f3ffc00307c000

def z131 : W := mkw 0x0802012001004400 0x2100402400200880 0xbda601208701c49f 0x77b4c02410e03893

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x98004603e0000000 0x130008c07c000000

def z133 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x033ffe001ffe0000 0xc067ffc003ffc000

def z134 : W := mkw 0xf51ff7ffe86ea9ca 0xfea3fefffd0dd539 0xffdffffff8ffffff 0xfffbffffff1fffff

def z135 : W := mkw 0x8400004b000228c0 0x1080000960004518 0x8000000f000000e0 0x10000001e000001c

def z136 : W := mkw 0x1000020000448000 0x0200004000089000 0x1e81460000cf8003 0xa3d028c00019f000

def z137 : W := mkw 0x110002002044810a 0x0220004004089021 0x14010630e0c18719 0x028020c61c1830e3

def z138 : W := mkw 0x0a02192483114434 0x2140432490622886 0xa020012c8731c4ff 0x7404002590e6389f

def z139 : W := mkw 0xc01735fec0000000 0x7802e6bfd8000000 0xf4073fffe0000000 0x1e80e7fffc000000

def z140 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xda414613e0cfa39a 0x9b4828c27c19f473

def z141 : W := mkw 0x8400004b000228c0 0x1080000960004518 0xe9c081cf003078e6 0x7d381039e0060f1c

def z142 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xfe81fe3fe0000000 0x1fd03fc7fc000000

def z143 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x66c101f000c07f05 0xacd8203e00180fe0

def z144 : W := mkw 0xb03dee4a1efd8000 0xd607bdc943dfb000 0xffbfffcf1fff8003 0xfff7fff9e3fff000

def z145 : W := mkw 0x4a173db4c3114434 0x6942e7b698622886 0xbda7bf3ce731c4ff 0x77b4f7e79ce6389f

def z146 : W := mkw 0x0802012001004400 0x2100402400200880 0x0426002007000401 0x0084c00400e00080

def z147 : W := mkw 0x303dee901efd9200 0xc607bdd203dfb240 0x5ffffed01fffbb03 0xebffffda03fff760

def z148 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x8918c1cf183e58e2 0x51231839e307cb1c

def z149 : W := mkw 0x0015000014800000 0x0002a00002900000 0x07bf00001fc00001 0xe0f7e00003f80000

def z150 : W := mkw 0x0002112480000000 0x2000422490000000 0xbd86b92c80000000 0x17b0d72590000000

def z151 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x427900d01fc07f05 0xe84f201a03f80fe0

def z152 : W := mkw 0x0802012001004400 0x2100402400200880 0x25a6012007004405 0x64b4c02400e00880

def z153 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x0026000007000000 0x0004c00000e00000

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x0398000018000000 0xe073000003000000

def z155 : W := mkw 0xe408f44fc82a28c0 0xdc811e89f9054518 0xfbd8ffcff83e78e6 0xff7b1ff9ff07cf1c

def z156 : W := mkw 0x0000080002110000 0x0000010000422000 0x1da6b80007318003 0x63b4d70000e63000

def z157 : W := mkw 0x0a00080003114434 0x0140010000622886 0x0020000007018419 0x0004000000e03083

def z158 : W := mkw 0xb408c24b086ea8c0 0x96811849610dd518 0xffd9c7cf18fff8e7 0xfffb38f9e31fff1c

def z159 : W := mkw 0x0a02192483114434 0x2140432490622886 0x0126b90c0731c4ff 0x6024d72180e6389f

def z160 : W := mkw 0x24000001082a28c0 0x0480000021054518 0xeac04003183e78e6 0xfd5808006307cf1c

def z161 : W := mkw 0x0000000014800000 0x0000000002900000 0x002000001fc00001 0xe004000003f80000

def z162 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1c27fe0007ff8003 0x0384ffc000fff000

def z163 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffc1c73fe0ffe7ff 0xfff838e7fc1ffcff

def z164 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x015881cc183e78e6 0xe02b10398307cf1c

def z165 : W := mkw 0xf03de6da5cec8000 0xde07bcdb4b9d9000 0x421946d378ce0000 0x884328da6f19c000

def z166 : W := mkw 0x703fffb4defd8000 0xee07fff69bdfb000 0x1fbffe30ffff8003 0xe3f7ffc61ffff000

def z167 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x0219460000000000 0x004328c000000000

def z168 : W := mkw 0x0a02192483114434 0x2140432490622886 0x1426382087018419 0x0284c70410e03083

def z169 : W := mkw 0x2c1701b11daa7ec0 0x2582e03623b54fd8 0x67ff01f01ffe7fe7 0xecffe03e03ffcffc

def z170 : W := mkw 0x0802092003114400 0x2100412400622880 0x3da6b9200731c407 0x67b4d72400e63880

def z171 : W := mkw 0x3028ee000a7d8000 0xc6051dc0014fb000 0x1b98fe00183f8002 0xe3731fc00307f000

def z172 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec14633e0c02705 0xbfd828c67c1804e0

def z173 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000001849f 0x2000000000003093

def z174 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xe11eb9ffe0000000 0x1c23d73ffc000000

def z175 : W := mkw 0xb508c24b286ea9ca 0x96a11849650dd539 0xebd8c1cf18ffffff 0xfd7b1839e31fffff

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x05a6000007000001 0x60b4c00000e00000

def z177 : W := mkw 0xc00211fec0000000 0x3800423fd8000000 0xfd86b9ffe0000000 0x1fb0d73ffc000000

def z178 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xffd9c7fff83e78e6 0xfffb38ffff07cf1c

def z179 : W := mkw 0xd03ffffed6d58000 0xfa07ffffdadab000 0xffbfffffe7c18001 0x1ff7fffffcf83000

def z180 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67bf01f007c00701 0x0cf7e03e00f800e0

def z181 : W := mkw 0x201dc0001ca80000 0x8403b80003950000 0x0fbfc0001ffe0003 0xe1f7f80003ffc000

def z182 : W := mkw 0xae0ad16f892a6cf4 0xb5c15a2df1254d9e 0xebd8c1ef983e7cfe 0xfd7b183df307cf9f

def z183 : W := mkw 0xca1ffdfec3114434 0xf943ffbfd8622886 0xffbfffffe7304060 0x5ff7fffffce6080c

def z184 : W := mkw 0x1000020000448000 0x0200004000089000 0x7ec1463000cfa707 0xafd828c60019f4e0

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c80000000018003 0x2390000000003000

def z186 : W := mkw 0x081701b001004400 0x2102e03600200880 0x67bf01f007004405 0x6cf7e03e00e00880

def z187 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67bf01f01f005800 0x4cf7e03e03e00b00

def z188 : W := mkw 0x0002012000000000 0x2000402400000000 0x2586012000000000 0x04b0c02400000000

def z189 : W := mkw 0x10202e0002558000 0x420405c0004ab000 0x10003e0000018000 0x020007c000003000

def z190 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x467f00f01fc03f01 0x88cfe01e03f807e0

def z191 : W := mkw 0x2e0008010b3b6cf4 0x05c0010021676d9e 0x006000001f3ffcff 0xe00c000003e7ff9f

def z192 : W := mkw 0xe03ffdfedeb90000 0xfc07ffbfdbd72000 0x013eb9cc1f300000 0x4027d73983e60000

def z193 : W := mkw 0x0a02192483114434 0x2140432490622886 0xffe7b93c87f1e7ff 0xfffcf72790fe3cff

def z194 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x1ec1460000cfa79f 0xa3d828c00019f4f3

def z195 : W := mkw 0x0802012001004400 0x2100402400200880 0x0126010007004000 0x4024c02000e00800

def z196 : W := mkw 0x0a00180483114434 0x0140030090622886 0x9820b80c8731c4ff 0x7304170190e6389f

def z197 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x1dbeb8001f318003 0x63b7d70003e63000

def z198 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0x5f9ffed360000000 0x0bf3ffda6c000000

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e81460000000000 0x03d028c000000000

def z200 : W := mkw 0x0a02192483114434 0x2140432490622886 0x1526b92c8731c479 0x42a4d72590e6388f

def z201 : W := mkw 0x881fc1fa15805600 0xb103f83f42b00ac0 0xefffc1ff1fc07f05 0xfdfff83fe3f80fe0

def z202 : W := mkw 0x0200180482110034 0x0040030090422006 0x9800b80c803180fa 0x130017019006301f

def z203 : W := mkw 0x0002112480000000 0x2000422490000000 0xa000012c80000000 0x1400002590000000

def z204 : W := mkw 0xb508c24b286ea9ca 0x96a11849650dd539 0xfed946f3f8cfbf9f 0xbfdb28de7f19f7f3

def z205 : W := mkw 0xc81fe5fa55805600 0xf903fcbf4ab00ac0 0x67ff47f37fc07f05 0xecffe8fe6ff80fe0

def z206 : W := mkw 0xc41ff5ffc0022080 0xf883febff8004410 0xffdfffffe00e2086 0xbffbfffffc01c410

def z207 : W := mkw 0x0015009014801200 0x0002a01202900240 0x47ff00d01fc03b01 0xe8ffe01a03f80760

def z208 : W := mkw 0x11352e0036d5810a 0x4226a5c006dab021 0x14273e30e7c18719 0x0284e7c61cf830e3

def z209 : W := mkw 0x0008c00000000000 0x8001180000000000 0x0b98c00000000000 0x0173180000000000

def z210 : W := mkw 0x151de6012046a18a 0xc2a3bcc02408d431 0xffdffe33e0cfa79f 0xbffbffc67c19f4f3

def z211 : W := mkw 0x0f021125a10265be 0x21e04224b4204cb7 0xe040013fe00067fc 0x1c080027fc000cff

def z212 : W := mkw 0xc81711fed5805600 0x3902e23fdab00ac0 0xe7ff01ffffc07f05 0xfcffe03ffff80fe0

def z213 : W := mkw 0x3028ca001efd8000 0x8605194003dfb000 0x0bb8c0001fff8003 0xe177180003fff000

def z214 : W := mkw 0xc21ffdfec2110034 0xf843ffbfd8422006 0xff9fffffe03180fa 0x1ff3fffffc06301f

def z215 : W := mkw 0x050000012002218a 0x00a0000024004431 0xe0400033e000279c 0x1c0800067c0004f3

def z216 : W := mkw 0x10000a0002558000 0x02000140004ab000 0x1fa7fe0007ff8003 0xe3f4ffc000fff000

def z217 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xffbffe33ffff8003 0xfff7ffc67ffff000

def z218 : W := mkw 0x0000009000001200 0x0000001200000240 0x404000d000003b00 0x0808001a00000760

def z219 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xffd8c1ef983ffcff 0xfffb183df307ff9f

def z220 : W := mkw 0x001701b014801200 0x2002e03602900240 0x67df01f018c03b00 0x8cfbe03e03180760

def z221 : W := mkw 0x001701b000000000 0x2002e03600000000 0x67df01f000c02705 0xacfbe03e001804e0

def z222 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x011eb9cc00000000 0x0023d73980000000

def z223 : W := mkw 0x281fc1b01da85600 0xa503f83603b50ac0 0x6fffc1f01ffe7f07 0xedfff83e03ffcfe0

def z224 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x000001c000005800 0x0000003800000b00

def z225 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x9c07fe3fe0000000 0x1380ffc7fc000000

def z226 : W := mkw 0x110002002044810a 0x0220004004089021 0x76c10630e0c1a71d 0xaed820c61c1834e3

def z227 : W := mkw 0x0200180482110034 0x0040030090422006 0x0000b80c00300060 0x000017018006000c

def z228 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xeac1461360ce2386 0xbd5828c26c19c470

def z229 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x053f01f01fc05f01 0x40a7e03e03f80be0

def z230 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x437f01d01fc07b00 0xc86fe03a03f80f60

def z231 : W := mkw 0x001701b000000000 0x2002e03600000000 0x67df01f018007804 0xecfbe03e03000f00

def z232 : W := mkw 0x203de4001ca80000 0xc407bc8003950000 0x0018000018000000 0x0003000003000000

def z233 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff47f3ffc07f05 0xffffe8fe7ff80fe0

def z234 : W := mkw 0x35200a013effa18a 0x06a4014027dff431 0xfee14633ffffa79f 0xffdc28c67ffff4f3

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x2480002000000405 0x2490000400000080

def z236 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x0000003000000700 0x00000006000000e0

def z237 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x7fffffc01ffff807 0xeffffff803ffff00

def z238 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x0020000007c00701 0x0004000000f800e0

def z239 : W := mkw 0x0000080002110000 0x0000010000422000 0x0020000007318003 0x6004000000e63000

def z240 : W := mkw 0xc01df44ec0000000 0xd803be89d8000000 0x9f9ffe0fe0000000 0x13f3ffc1fc000000

def z241 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x4241461360ce2300 0x884828c26c19c460

def z242 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xfb98ffcfe0000000 0x1f731ff9fc000000

def z243 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0xffffb9fc9fc07f05 0xfffff73f93f80fe0

def z244 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xfe877e33e0000000 0x1fd0efc67c000000

def z245 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x002000001f005800 0x4004000003e00b00

def z246 : W := mkw 0xec1ff5ffddaa7ec0 0xfd83febffbb54fd8 0xfffffffffffe7fe7 0xffffffffffffcffc

def z247 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xe840c1cf003e78e6 0x1d081839e007cf1c

def z248 : W := mkw 0x0a02192483114434 0x2140432490622886 0x9c26b82c873184fb 0x1384d70590e6309f

def z249 : W := mkw 0xca1ffdfec3114434 0xf943ffbfd8622886 0xffbfffffe7018419 0x1ff7fffffce03083

def z250 : W := mkw 0x1515029134c6b38a 0x02a2a0522698d671 0x425946d378ce3b00 0x884b28da6f19c760

def z251 : W := mkw 0x801fc1fa00000000 0xb003f83f40000000 0xef9fc1ff00000000 0x1df3f83fe0000000

def z252 : W := mkw 0x3508c201286ea18a 0x86a11840250dd431 0xffd9c633f8ffa79f 0xfffb38c67f1ff4f3

def z253 : W := mkw 0x15352e0136d7a18a 0x42a6a5c026daf431 0xfee77e33e7cfa79f 0xbfdcefc67cf9f4f3

def z254 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff01f09fc1ff9f 0xffffe03e13f83ff3

def z255 : W := mkw 0x1d1703b135c6f78a 0x23a2e07626b8def1 0xfee74633e7cfa79f 0xbfdce8c67cf9f4f3

def z256 : W := mkw 0xac1fc1fb1daa7ec0 0xb583f83f63b54fd8 0x67ff41f31fce7f05 0xecffe83e63f9cfe0

def z257 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x023946001fff8003 0xe04728c003fff000

def z258 : W := mkw 0xa008c04a08280840 0x9401180941050108 0xeb98c1cf18305860 0x5d731839e3060b0c

def z259 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x193efe001f3f8002 0x4327dfc003e7f000

def z260 : W := mkw 0x0015009014801200 0x0002a01202900240 0x66d900f018c03f05 0xacdb201e031807e0

def z261 : W := mkw 0x303de6001cec8000 0xc607bcc0039d9000 0x1e99460018cf8003 0xa3d328c00319f000

def z262 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbca638208701849f 0x3794c70410e03093

def z263 : W := mkw 0x0002112480000000 0x2000422490000000 0xbd86b92c803040e6 0x77b0d7259006081c

def z264 : W := mkw 0x0400000100022080 0x0080000020004410 0xfec14633e00e2086 0xbfd828c67c01c410

def z265 : W := mkw 0x1d1703b135c6f78a 0x23a2e07626b8def1 0xffff47f3ffcfff9f 0xffffe8fe7ff9fff3

def z266 : W := mkw 0xa008c04a08280840 0x9401180941050108 0x63d881cc18307864 0xec7b103983060f0c

def z267 : W := mkw 0xb43dee4b1effa8c0 0xd687bdc963dff518 0x9fbffe0f1fff80e3 0xf3f7ffc1e3fff01c

def z268 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x4bd8c0c3183e3802 0xe97b18186307c700

def z269 : W := mkw 0xd51de6db6046a18a 0xdaa3bcdb6c08d431 0xfed946f3e0cfa79f 0xbfdb28de7c19f4f3

def z270 : W := mkw 0x30352e001efd8000 0x4606a5c003dfb000 0x14273e001fff8003 0xe284e7c003fff000

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0x2180010000004004 0x6430002000000800

def z272 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xbc804623e00f849f 0x379008c47c01f093

def z273 : W := mkw 0x0200180482110034 0x0040030090422006 0x1000380080018018 0x0200070010003003

def z274 : W := mkw 0x191703b035c4d70a 0x2322e07606b89ae1 0x14270630e7c18719 0x0284e0c61cf830e3

def z275 : W := mkw 0x0a02092003114434 0x2140412400622886 0x25a601200731c4ff 0x64b4c02400e6389f

def z276 : W := mkw 0x00352c0016910000 0x4006a58002d22000 0x0026380007000000 0x0004c70000e00000

def z277 : W := mkw 0x0000000014801200 0x0000000002900240 0x0040000018c03b00 0x8008000003180760

def z278 : W := mkw 0xb508c24b286ea9ca 0x96a11849650dd539 0xfbd8c7cff83ff8fe 0xff7b18f9ff07ff1f

def z279 : W := mkw 0xa008c04a08280840 0x9401180941050108 0x001800c018001800 0x0003001803000300

def z280 : W := mkw 0x001701b000000000 0x2002e03600000000 0x011e01c000000000 0x0023c03800000000

def z281 : W := mkw 0x10352e0016d58000 0x4206a5c002dab000 0x17bf3e001fc18001 0xe2f7e7c003f83000

def z282 : W := mkw 0x0400000100022080 0x0080000020004410 0xebc0c10f003e60e6 0xfd781821e007cc1c

def z283 : W := mkw 0x0a02192483114434 0x2140432490622886 0xa9a6b90c073040e6 0x7534d72180e6081c

def z284 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x63d841c3180e7804 0xec7b08386301cf00

def z285 : W := mkw 0xf83ffffedffdd600 0xff07ffffdbffbac0 0xffffffffffffff07 0xffffffffffffffe0

def z286 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xbd87bf3ce0000000 0x17b0f7e79c000000

def z287 : W := mkw 0x0400000100022080 0x0080000020004410 0xfec04023800fa49f 0xbfd808047001f493

def z288 : W := mkw 0x0400000100022080 0x0080000020004410 0xebd841c3180e7886 0xfd7b08386301cf10

def z289 : W := mkw 0xae0ad96f8b3b6cf4 0xb5c15b2df1676d9e 0xebfef9cf1f3e78e6 0xfd7fdf39e3e7cf1c

def z290 : W := mkw 0x3528ee012a7fa18a 0xc6a51dc0254ff431 0x9800fe03e03f809a 0x13001fc07c07f013

def z291 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x66e7003007c02705 0xacdce00600f804e0

def z292 : W := mkw 0x050000012002218a 0x00a0000024004431 0xfcc00033e001a79f 0x3f9800067c0034f3

def z293 : W := mkw 0xc00211fec0000000 0x3800423fd8000000 0x000001cc00000000 0x0000003980000000

def z294 : W := mkw 0x8e02116f81026cf4 0x31c0422df0204d9e 0xe04001ef80007cfc 0x1c08003df0000f9f

def z295 : W := mkw 0x0015009014801200 0x0002a01202900240 0x63d901d018c07b04 0xec7b203a03180f60

def z296 : W := mkw 0x0015000014800000 0x0002a00002900000 0x013e00001f000000 0x4027c00003e00000

def z297 : W := mkw 0x0200180482110034 0x0040030090422006 0x9da6b80c873180fb 0x73b4d70190e6301f

def z298 : W := mkw 0xbf0adb6fab7fedfe 0xb7e15b6df56ffdbf 0xffffffffffffffff 0xffffffffffffffff

def z299 : W := mkw 0xac1fc1fb1daa7ec0 0xb583f83f63b54fd8 0xebfec1cf1f3e78e6 0xfd7fd839e3e7cf1c

def z300 : W := mkw 0x1000020000448000 0x0200004000089000 0xbe81462080cf849f 0xb7d028c41019f093

def z301 : W := mkw 0x1b021b24a355c53e 0x23604364946ab8a7 0x14273e30e7c18719 0x0284e7c61cf830e3

def z302 : W := mkw 0x081709b017915600 0x2102e13602f22ac0 0x7fffb9f01ff1ff07 0xeffff73e03fe3fe0

def z303 : W := mkw 0xca0211fec1004434 0x3940423fd8200886 0xe00001ffe00044fc 0x1c00003ffc00089f

def z304 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x0bbef8001f3e0002 0xe177df0003e7c000

def z305 : W := mkw 0x050000012002218a 0x00a0000024004431 0xfec14633e000279c 0x1fd828c67c0004f3

def z306 : W := mkw 0x110002002044810a 0x0220004004089021 0xfe814633e0c18719 0x1fd028c67c1830e3

def z307 : W := mkw 0xca1ffdfed7915634 0xf943ffbfdaf22ac6 0xfffffffffff1ffff 0xfffffffffffe3fff

def z308 : W := mkw 0xa608d84f8a3b28f4 0x94c11b09f147651e 0xfbd8f9cf983ff8fe 0xff7b1f39f307ff1f

def z309 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0x013eb9cc1f005800 0x4027d73983e00b00

def z310 : W := mkw 0x2008c00008280000 0x8401180001050000 0xab98c10c183e40e6 0xf57318218307c81c

def z311 : W := mkw 0xdd1ff7fff5c6f78a 0xfba3fefffeb8def1 0xffffffffffcfff9f 0xfffffffffff9fff3

def z312 : W := mkw 0x30200a000a7d8000 0x06040140014fb000 0x00000000003f8002 0x000000000007f000

def z313 : W := mkw 0x0a1719b497915634 0x2142e33692f22ac6 0x67ffb9fc1ff07f65 0xecfff73f83fe0fec

def z314 : W := mkw 0x24000001082a28c0 0x0480000021054518 0x00400000180e3800 0x800800000301c700

def z315 : W := mkw 0x1515020134c6a18a 0x02a2a0402698d431 0xffff4633ffcfa79f 0xffffe8c67ff9f4f3

def z316 : W := mkw 0x303fff249efd8000 0xe607ffe493dfb000 0xbfbfff2c9fff8003 0xf7f7ffe593fff000

def z317 : W := mkw 0xae08c84b0b3b6cf4 0x95c1190961676d9e 0xebf8c1cf1f3ffcff 0xfd7f1839e3e7ff9f

def z318 : W := mkw 0xf43fffffdeffa8c0 0xfe87fffffbdff518 0xfffffffffffff8e7 0xffffffffffffff1c

def z319 : W := mkw 0x0a00080017915634 0x0140010002f22ac6 0x006000001ff1ffff 0xe00c000003fe3fff

def z320 : W := mkw 0x0a02192483114434 0x2140432490622886 0x1da6b8208731841b 0x63b4d70410e63083

def z321 : W := mkw 0xd508f64fe046a18a 0xdaa11ec9fc08d431 0xfec1fe3fe0cfa79f 0xbfd83fc7fc19f4f3

def z322 : W := mkw 0x0008e40000000000 0xc0011c8000000000 0x1800fe0000000000 0x03001fc000000000

def z323 : W := mkw 0xa008c04a08280840 0x9401180941050108 0xa99881cc183058e6 0x7533103983060b1c

def z324 : W := mkw 0xa43dec4b1ebb28c0 0xd487bd8963d76518 0xebfef9cf1f3e78e6 0xfd7fdf39e3e7cf1c

def z325 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x1fbffe001f300000 0x43f7ffc003e60000

def z326 : W := mkw 0x0015009014801200 0x0002a01202900240 0x001800c018001800 0x0003001803000300

def z327 : W := mkw 0x0000000000000000 0x0000000000000000 0x425800c018003800 0x884b001803000700

def z328 : W := mkw 0x383fe7b01decd600 0xe707fcf603bd9ac0 0x67ff47f01fce7f05 0xecffe8fe03f9cfe0

def z329 : W := mkw 0x353de6013ceea18a 0xc6a7bcc0279dd431 0x4259461378ce2300 0x884b28c26f19c460

def z330 : W := mkw 0x3528ee012a7fa18a 0xc6a51dc0254ff431 0xfec1fe33e0ffa79f 0xbfd83fc67c1ff4f3

def z331 : W := mkw 0x0802012001004400 0x2100402400200880 0x67e7013007c06705 0xecfce02600f80ce0

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x14010630e0000000 0x028020c61c000000

def z333 : W := mkw 0x001fe5b000000000 0xe003fcb600000000 0x7f9ffff000000000 0x0ff3fffe00000000

def z334 : W := mkw 0xb53dee4b3effa9ca 0xd6a7bdc967dff539 0xffffffffffffffff 0xffffffffffffffff

def z335 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbda6b92c87304060 0x57b4d72590e6080c

def z336 : W := mkw 0x8e02196f83136cf4 0x31c0432df0626d9e 0xfde6b9ef8731fcff 0x7fbcd73df0e63f9f

def z337 : W := mkw 0xf028fe4eca7d8000 0xde051fc9d94fb000 0x9800fe0fe03f8002 0x13001fc1fc07f000

def z338 : W := mkw 0x8000004a00000000 0x1000000940000000 0xe00001cf00000000 0x1c000039e0000000

def z339 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x046700301fc07f05 0xe08ce00603f80fe0

def z340 : W := mkw 0xe41ff5ffc82a28c0 0xfc83febff9054518 0xff9fffffe03e00e2 0x1ff3fffffc07c01c

def z341 : W := mkw 0x0a1719b497915634 0x2142e33692f22ac6 0xbda7b93c87f1c7ff 0x77b4f72790fe38ff

def z342 : W := mkw 0x8008c04a00000000 0x9001180940000000 0xeb98c1cf003040e6 0x7d731839e006081c

def z343 : W := mkw 0xb508c24b286ea9ca 0x96a11849650dd539 0x425946d378ce3b00 0x884b28da6f19c760

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100810c00304060 0x402010218006080c

def z345 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xbcc0002080cfa79f 0xb79800041019f4f3

def z346 : W := mkw 0xa400004b082a28c0 0x1480000961054518 0xe04001cf183e78e6 0xfc080039e307cf1c

def z347 : W := mkw 0xae1fd9ff9fbb7ef4 0xb5c3fb3ff3f76fde 0xfffff9ff9fffffff 0xffffff3ff3ffffff

def z348 : W := mkw 0x0a02192483114434 0x2140432490622886 0x9926b90c8731c0fa 0x5324d72190e6381f

def z349 : W := mkw 0x8008c04a00000000 0x9001180940000000 0x8800c00f00000000 0x11001801e0000000

def z350 : W := mkw 0xc00ad1fec0000000 0xb8015a3fd8000000 0xeb98c1ffe0000000 0x1d73183ffc000000

def z351 : W := mkw 0x110002002044810a 0x0220004004089021 0x1e814630e0cf871b 0xa3d028c61c19f0e3

def z352 : W := mkw 0x103dee0016d58000 0xc207bdc002dab000 0x1fbffe0007c18001 0x03f7ffc000f83000

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0x1400002080018419 0x0280000410003083

def z354 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x163f7e001fcf8001 0x82c7efc003f9f000

def z355 : W := mkw 0x110002002044810a 0x0220004004089021 0x0000000000c18719 0x00000000001830e3

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x011801c018005800 0x4023003803000b00

def z357 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x4358c1cf183e7860 0xc86b1839e307cf0c

def z358 : W := mkw 0xb508c24b286ea9ca 0x96a11849650dd539 0xfec1c63fe0ffa7ff 0xbfd838c7fc1ff4ff

def z359 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xefff81fc1ff07fe7 0xfdfff03f83fe0ffc

def z360 : W := mkw 0xd508f64fe046a18a 0xdaa11ec9fc08d431 0x9800fe0fe00f809a 0x13001fc1fc01f013

def z361 : W := mkw 0xb43de64b1ceea8c0 0xd687bcc9639dd518 0x425946c318ce3800 0x884b28d86319c700

def z362 : W := mkw 0x9508c24b2046a18a 0x92a118496408d431 0xffd9c7ffe0cfa79f 0xbffb38fffc19f4f3

def z363 : W := mkw 0x1f000a012357e5be 0x03e00140246afcb7 0xfee14633e7ffe7ff 0xffdc28c67cfffcff

def z364 : W := mkw 0x2000000008280840 0x0400000001050108 0x0000000018305860 0x4000000003060b0c

def z365 : W := mkw 0xa41fc1fb082a28c0 0xb483f83f61054518 0xefdfc1ff183e78e6 0xfdfbf83fe307cf1c

def z366 : W := mkw 0x110002002044810a 0x0220004004089021 0xbc810630e0c1879f 0x379020c61c1830f3

def z367 : W := mkw 0x10352e0016d58000 0x4206a5c002dab000 0x1ea77e0007cf8003 0xa3d4efc000f9f000

def z368 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x66e100301fc07f05 0xecdc200603f80fe0

def z369 : W := mkw 0xe41ff5ffc82a28c0 0xfc83febff9054518 0xebdef9cf183e78e6 0xfd7bdf39e307cf1c

def z370 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfac04603e00fa09e 0xbf5808c07c01f413

def z371 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a804000000e0002 0xa15008000001c000

def z372 : W := mkw 0x1a373f2497d5c434 0x6346e7e492fab886 0xbda7bf2c87f1c4ff 0x77b4f7e590fe389f

def z373 : W := mkw 0xee1ffdffcb3b6cf4 0xfdc3ffbff9676d9e 0xffffffffff3ffcff 0xffffffffffe7ff9f

def z374 : W := mkw 0xc01df4dec0000000 0xd803be9bd8000000 0xda19fedfe0000000 0x1b433fdbfc000000

def z375 : W := mkw 0xc01ffdfec2110000 0xf803ffbfd8422000 0xffbfffffe7318003 0x7ff7fffffce63000

def z376 : W := mkw 0x1f021b25a357e5be 0x23e04364b46afcb7 0xbde6b92c87ffe7ff 0xf7bcd72590fffcff

def z377 : W := mkw 0x801de44a00000000 0xd003bc8940000000 0xff9fffcf00000000 0x1ff3fff9e0000000

def z378 : W := mkw 0x8408c04b000228c0 0x9081180960004518 0xebd8c1cf000078e4 0x1d7b1839e0000f1c

def z379 : W := mkw 0x2408c001082a28c0 0x8481180021054518 0x0bd8c000183e78e6 0xe17b18000307cf1c

def z380 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x00004603600e0000 0x000008c06c01c000

def z381 : W := mkw 0x001701b000000000 0x2002e03600000000 0x679f01f000000000 0x0cf3e03e00000000

def z382 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xbfbffe209fff849f 0xf7f7ffc413fff093

def z383 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xead840c3180e3886 0xbd5b08186301c710

def z384 : W := mkw 0xf03deeda5efd8000 0xde07bddb4bdfb000 0x5fbffed37fff8003 0xebf7ffda6ffff000

def z385 : W := mkw 0xa41dc0db1caa3ac0 0x9483b81b63954758 0x425940d318ce3b00 0x884b281a6319c760

def z386 : W := mkw 0x0000100480000000 0x0000020090000000 0x9800b80c80000000 0x1300170190000000

def z387 : W := mkw 0x30350a001efd8000 0x0606a14003dfb000 0x07bf00001fff8003 0xe0f7e00003fff000

def z388 : W := mkw 0x24000001082a28c0 0x0480000021054518 0x63d801c0183e78e6 0xec7b00380307cf1c

def z389 : W := mkw 0xb03dee4a1efd8840 0xd607bdc943dfb108 0x1fbfffcc1fffd863 0xe3f7fff983fffb0c

def z390 : W := mkw 0xae0ad96f8b3b6cf4 0xb5c15b2df1676d9e 0xbda6f92f873fc4ff 0x77b4df25f0e7f89f

def z391 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x0000b80c00000000 0x0000170180000000

def z392 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x013eb8001fff8003 0xe027d70003fff000

def z393 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x63f801c01fc07f05 0xec7f003803f80fe0

def z394 : W := mkw 0x001711b480000000 0x2002e23690000000 0xff9fb9fc80000000 0x1ff3f73f90000000

def z395 : W := mkw 0x0002112480000000 0x2000422490000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z396 : W := mkw 0xe41ff5ffc82a28c0 0xfc83febff9054518 0xffdffffff80e3800 0x9ffbffffff01c700

def z397 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xe15881cf183078e4 0x5c2b1039e3060f1c

def z398 : W := mkw 0x0015240000000000 0x4002a48000000000 0x14073e0000000000 0x0280e7c000000000

def z399 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x00000000000f809a 0x000000000001f013

def z400 : W := mkw 0x18372fb017d5d600 0x6306e5f602fabac0 0x77ff3ff01fc1ff05 0xeeffe7fe03f83fe0

def z401 : W := mkw 0x8000004a00000840 0x1000000940000108 0x000001cc00005860 0x0000003980000b0c

def z402 : W := mkw 0x0a02192483114434 0x2140432490622886 0x142638208731c4ff 0x6284c70410e6389f

def z403 : W := mkw 0x3a2aff248b7dc434 0xe7455fe4916fb886 0xbda6ff2c873fc4ff 0x77b4dfe590e7f89f

def z404 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe03040e6 0x7ff3fffffc06081c

def z405 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x011eb80000000000 0x0023d70000000000

def z406 : W := mkw 0xe01ff5fec8280840 0xfc03febfd9050108 0x011eb9cc18305860 0x4023d73983060b0c

def z407 : W := mkw 0x3028e600086c8000 0xc6051cc0010d9000 0x00004600000e0000 0x000008c00001c000

def z408 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfec14633e0ce2300 0x9fd828c67c19c460

def z409 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x0006380000000000 0x0000c70000000000

def z410 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67ff01c01fc07805 0xecffe03803f80f00

def z411 : W := mkw 0xb428ca4b1effa8c0 0x9685194963dff518 0xebf8c1cf1ffff8e7 0xfd7f1839e3ffff1c

def z412 : W := mkw 0x2a0ad9248b394434 0xa5415b2491672886 0xbfbef92c9f3fc4ff 0xf7f7df2593e7f89f

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800800c003000e2 0x110010018006001c

def z414 : W := mkw 0x1000020000448000 0x0200004000089000 0x0201460000ce0000 0x804028c00019c000

def z415 : W := mkw 0xe41de4db482a28c0 0xdc83bc9b69054518 0xebd9c7df783e78e6 0xfd7b38fbef07cf1c

def z416 : W := mkw 0x0000000000000000 0x0000000000000000 0x62c0000000002004 0xac58000000000400

def z417 : W := mkw 0xc01ff5fed4800000 0xf803febfda900000 0xffbfffffffc00001 0xfff7fffffff80000

def z418 : W := mkw 0xac0ac1fb092a7ec0 0xb581583f61254fd8 0xebd8c1ff183e7fe6 0xfd7b183fe307cffc

def z419 : W := mkw 0x40003404c0000000 0x4800068098000000 0x10003e00e0000000 0x020007c01c000000

def z420 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67ff00301fc02705 0xecffe00603f804e0

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0xea80400300000000 0x1d50080060000000

def z422 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xeb9ef9cf00000000 0x1d73df39e0000000

def z423 : W := mkw 0xe01ff5fec8280840 0xfc03febfd9050108 0xff9ffffff8305860 0x5ff3ffffff060b0c

def z424 : W := mkw 0xe41de4db482a28c0 0xdc83bc9b69054518 0x425946d3780e3800 0x884b28da6f01c700

def z425 : W := mkw 0x0800000001004400 0x0100000000200880 0x0020000007004405 0x6004000000e00880

def z426 : W := mkw 0x0817012015804400 0x2102e02402b00880 0x27bf01201fc04405 0xe4f7e02403f80880

def z427 : W := mkw 0x1f000a012357e5be 0x03e00140246afcb7 0x0060000007ffe7ff 0xe00c000000fffcff

def z428 : W := mkw 0x0a1719b497915634 0x2142e33692f22ac6 0x77ff39f09fc1ff1d 0xeeffe73e13f83fe3

def z429 : W := mkw 0x0000080002110000 0x0000010000422000 0xbda6b8208731849f 0x77b4d70410e63093

def z430 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x7ffffe301fffa707 0xefffffc603fff4e0

def z431 : W := mkw 0x0a02192483114434 0x2140432490622886 0x1da6b90c0731c063 0x63b4d72180e6380c

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0x6040003000002704 0x0c080006000004e0

def z433 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x4241461360cfa79f 0xa84828c26c19f4f3

def z434 : W := mkw 0x0802012001004400 0x2100402400200880 0x2000012000004404 0x0400002400000880

def z435 : W := mkw 0x0000000000000000 0x0000000000000000 0x0681000000c00001 0xa0d0200000180000

def z436 : W := mkw 0x383fefb01ffdd600 0xe707fdf603ffbac0 0x1fbffe301fff8703 0xe3f7ffc603fff0e0

def z437 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d86b80000000000 0x03b0d70000000000

def z438 : W := mkw 0xdf1fffffe357e5be 0xfbe3fffffc6afcb7 0xffffffffe7ffe7ff 0xfffffffffcfffcff

def z439 : W := mkw 0x8c0201fb01027ec0 0x3180403f60204fd8 0xe04001ff00007fe4 0x1c08003fe0000ffc

def z440 : W := mkw 0x0400000100022080 0x0080000020004410 0x00400000000e2086 0xa00800000001c410

def z441 : W := mkw 0x353dee013effa18a 0xc6a7bdc027dff431 0x1ffffe001fffa79f 0xe3ffffc003fff4f3

def z442 : W := mkw 0xb508c24b286ea9ca 0x96a11849650dd539 0xebd9c7df78fe7be6 0xfd7b38fbef1fcf7c

def z443 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xbfbfff0c1fffc0e7 0xf7f7ffe183fff81c

def z444 : W := mkw 0x800ad16e80000000 0xb0015a2dd0000000 0xff9ef9ef80000000 0x1ff3df3df0000000

def z445 : W := mkw 0x303de6001cec8000 0xc607bcc0039d9000 0x0b99c60018fe0002 0xe17338c0031fc000

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000000c02705 0xa0080000001804e0

def z447 : W := mkw 0x3a200a001ffdc434 0x0744014003ffb886 0x002000001fffc4ff 0xe004000003fff89f

def z448 : W := mkw 0x0000080002110000 0x0000010000422000 0xbda6b90c0731c0e7 0x77b4d72180e6381c

def z449 : W := mkw 0x001de40014800000 0xc003bc8002900000 0x1fbffe001fc00001 0xe3f7ffc003f80000

def z450 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x66c1003000cfa79f 0xacd820060019f4f3

def z451 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x0040000000ce2300 0x800800000019c460

def z452 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x017e01c01fc07f05 0xe02fc03803f80fe0

def z453 : W := mkw 0xc41ff5ffc00228c0 0xf883febff8004518 0xffdfffffe00078e4 0x1ffbfffffc000f1c

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x980000008001809a 0x1300000010003013

def z455 : W := mkw 0xd51ff7ffe046a18a 0xfaa3fefffc08d431 0xffdfffffe0ce2300 0x9ffbfffffc19c460

def z456 : W := mkw 0xa03dec4a1eb90840 0xd407bd8943d72108 0x013eb9cc1f305860 0x4027d73983e60b0c

def z457 : W := mkw 0x1f021b25a357e5be 0x23e04364b46afcb7 0xbda6ff2fe73fc4ff 0x77b4dfe5fce7f89f

def z458 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x9c014633e0cf879b 0x138028c67c19f0f3

def z459 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000018007804 0xe008000003000f00

def z460 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x625901f018c07f04 0x8c4b203e03180fe0

def z461 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xf8404633e00fa79e 0x1f0808c67c01f4f3

def z462 : W := mkw 0x8c1701fb15827ec0 0x3182e03f62b04fd8 0xe7ff01ff1fc07fe5 0xfcffe03fe3f80ffc

def z463 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1a19fe0018ff8002 0x83433fc0031ff000

def z464 : W := mkw 0x3228fe048a7d8034 0xc6451fc0914fb006 0x9800fe0c803f80fa 0x13001fc19007f01f

def z465 : W := mkw 0xb43de64b1ceea8c0 0xd687bcc9639dd518 0xebd9c7cf18fe78e6 0xfd7b38f9e31fcf1c

def z466 : W := mkw 0x1515029134c6b38a 0x02a2a0522698d671 0xfed946f3f8cfbf9f 0xbfdb28de7f19f7f3

def z467 : W := mkw 0x081701b001005600 0x2102e03600200ac0 0x67df01f000007f04 0x0cfbe03e00000fe0

def z468 : W := mkw 0x0015080016910000 0x0002a10002d22000 0x1fbfb8001ff18003 0xe3f7f70003fe3000

def z469 : W := mkw 0x0a0211b481005634 0x2140423690200ac6 0xe04001fc80007ffc 0x1c08003f90000fff

def z470 : W := mkw 0x8400004b000228c0 0x1080000960004518 0xe3d801cf180078e4 0xfc7b0039e3000f1c

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x67d901f018c07f05 0xecfb203e03180fe0

def z472 : W := mkw 0x1d1703b135c6f78a 0x23a2e07626b8def1 0x67ff01f01fcfff9f 0xecffe03e03f9fff3

def z473 : W := mkw 0xca1ffdfec3114434 0xf943ffbfd8622886 0xbdbeb9ec8731c4ff 0x77b7d73d90e6389f

def z474 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x646701f007c07f05 0x0c8ce03e00f80fe0

def z475 : W := mkw 0x050000012002218a 0x00a0000024004431 0xeac04033e00e279e 0xbd5808067c01c4f3

def z476 : W := mkw 0x1d00020135c6f78a 0x03a0004026b8def1 0xfee14633ffcfff9f 0xffdc28c67ff9fff3

def z477 : W := mkw 0x0000080002110000 0x0000010000422000 0x0126b80007300000 0x4024d70000e60000

def z478 : W := mkw 0x110002002044810a 0x0220004004089021 0x0001061060c00300 0x000020c20c180060

def z479 : W := mkw 0x38200a001ffdd600 0x0704014003ffbac0 0x006000001fffff07 0xe00c000003ffffe0

def z480 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x8b98c00f183e00e2 0xf1731801e307c01c

def z481 : W := mkw 0xb508c24b286ea9ca 0x96a11849650dd539 0x9800c60fe03f80fa 0x130018c1fc07f01f

def z482 : W := mkw 0x2c0000011daa7ec0 0x0580000023b54fd8 0x006000001ffe7fe7 0xe00c000003ffcffc

def z483 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x151fbffce0000000 0x02a3f7ff9c000000

def z484 : W := mkw 0xd51de6db6046a18a 0xdaa3bcdb6c08d431 0x425946d360ce2300 0x884b28da6c19c460

def z485 : W := mkw 0x050000012002218a 0x00a0000024004431 0x004000000000279c 0x00080000000004f3

def z486 : W := mkw 0x101de60000448000 0xc203bcc000089000 0x1f9ffe0000cf8003 0xa3f3ffc00019f000

def z487 : W := mkw 0x2000000008280000 0x0400000001050000 0x00000000183e0002 0xe00000000307c000

def z488 : W := mkw 0xc40211ffc00228c0 0x3880423ff8004518 0xe04001ffe00078e4 0x1c08003ffc000f1c

def z489 : W := mkw 0x323dfe049efd8034 0xc647bfc093dfb006 0x9fbffe0c9fff80fb 0xf3f7ffc193fff01f

def z490 : W := mkw 0x0400000100022080 0x0080000020004410 0xe040000300002084 0x1c08000060000410

def z491 : W := mkw 0x0a00080003114434 0x0140010000622886 0xa9a0810c0731c4ff 0x7534102180e6389f

def z492 : W := mkw 0x353dee013effa18a 0xc6a7bdc027dff431 0x9fbffe03ffff809b 0xf3f7ffc07ffff013

def z493 : W := mkw 0x302002001cec8000 0x06040040039d9000 0x0000000018ce0000 0x800000000319c000

def z494 : W := mkw 0xa41dc0db1caa3ac0 0x9483b81b63954758 0xebd9c1df18fe7be6 0xfd7b383be31fcf7c

def z495 : W := mkw 0x383fefb01ffdd600 0xe707fdf603ffbac0 0x1fbfffc01fffd803 0xe3f7fff803fffb00

def z496 : W := mkw 0x313dee003efd810a 0xc627bdc007dfb021 0x1fbffe30ffff871b 0xe3f7ffc61ffff0e3

def z497 : W := mkw 0x3a3dee001ffdc434 0xc747bdc003ffb886 0x1fbffe001fffc4ff 0xe3f7ffc003fff89f

def z498 : W := mkw 0x383fef201ffdc400 0xe707fde403ffb880 0x3fbfff201fffc407 0xe7f7ffe403fff880

def z499 : W := mkw 0xc008e44a40000000 0xd8011c8948000000 0x0000460360000000 0x000008c06c000000

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000208000049c 0x1400000410000093

def z501 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0xfe9946f3e0000000 0x1fd328de7c000000

def z502 : W := mkw 0x0002112480000000 0x2000422490000000 0x1406382080000000 0x0280c70410000000

def z503 : W := mkw 0x140002010046a080 0x028000402008d410 0xfec1460300cfa087 0xbfd828c06019f410

def z504 : W := mkw 0x8500004b200229ca 0x10a0000964004539 0xe04001ffe0007ffc 0x1c08003ffc000fff

def z505 : W := mkw 0x0a1ffd2483114434 0xe143ffa490622886 0xbfbfff2c8731c4ff 0x77f7ffe590e6389f

def z506 : W := mkw 0x8400004b000228c0 0x1080000960004518 0xeac041cf000e78e6 0xbd580839e001cf1c

def z507 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x779f3ff0e0000000 0x0ef3e7fe1c000000

def z508 : W := mkw 0x8a0ad96e83114434 0xb1415b2dd0622886 0xffbef9ef8731c4ff 0x7ff7df3df0e6389f

def z509 : W := mkw 0x0815000015805600 0x0102a00002b00ac0 0x07ff00001fc07f05 0xe0ffe00003f80fe0

def z510 : W := mkw 0xb428ee4b0a7fa8c0 0xd6851dc9614ff518 0xfbd8ffcf183ff8e6 0xff7b1ff9e307ff1c

def z511 : W := mkw 0xa608d84f8a3b28f4 0x94c11b09f147651e 0x9800f80f803f80fa 0x13001f01f007f01f

def z512 : W := mkw 0xca0219fec3114434 0x3940433fd8622886 0xfda6b9ffe731c4ff 0x7fb4d73ffce6389f

def z513 : W := mkw 0x1f021325a146e5be 0x23e04264b428dcb7 0xfec1473fe0cfe7ff 0xbfd828e7fc19fcff

def z514 : W := mkw 0x10352e0016d58000 0x4206a5c002dab000 0x1da7be0007f18003 0x63b4f7c000fe3000

def z515 : W := mkw 0x0400000100022080 0x0080000020004410 0x42404003000e2000 0x884808006001c400

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0xa880000000000086 0x3510000000000010

def z517 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x25be01e01f005c05 0x64b7c03c03e00b80

def z518 : W := mkw 0x383dee001ffdd600 0xc707bdc003ffbac0 0x1ffffe001fffff07 0xe3ffffc003ffffe0

def z519 : W := mkw 0x050000012002218a 0x00a0000024004431 0x4040001360002300 0x080800026c000460

def z520 : W := mkw 0xe40ad1ffc82a28c0 0xbc815a3ff9054518 0xebd8c1fff83e78e6 0xfd7b183fff07cf1c

def z521 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfe814633e00f809a 0x1fd028c67c01f013

def z522 : W := mkw 0x1035260014c48000 0x4206a4c002989000 0x0001060000c00000 0x000020c000180000

def z523 : W := mkw 0xd11ff7fee044810a 0xfa23feffdc089021 0xff9fffffe0c18719 0x1ff3fffffc1830e3

def z524 : W := mkw 0x400211b4c0000000 0x2800423698000000 0x00000030e0000000 0x000000061c000000

def z525 : W := mkw 0x010000002000010a 0x0020000004000021 0x00000030e0000718 0x000000061c0000e3

def z526 : W := mkw 0x0a02112481004434 0x2140422490200886 0xbd86b92c800044fc 0x17b0d7259000089f

def z527 : W := mkw 0x50373fb4d6d58000 0x6a06e7f69adab000 0x14273e30e7c18001 0x0284e7c61cf83000

def z528 : W := mkw 0x3a3fff249ffdc434 0xe747ffe493ffb886 0x1fbffe209fff841b 0xe3f7ffc413fff083

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000003040e6 0x600000000006081c

def z530 : W := mkw 0xbc3feffb1ffffec0 0xf787fdff63ffffd8 0xffffffff1fffffe7 0xffffffffe3fffffc

def z531 : W := mkw 0x1d0203b12146f78a 0x23a040762428def1 0xfec147f3e0cfff9f 0xbfd828fe7c19fff3

def z532 : W := mkw 0xf03dfe4edefd8000 0xde07bfc9dbdfb000 0x9fbffe0fffff8003 0xf3f7ffc1fffff000

def z533 : W := mkw 0x0a00080003114434 0x0140010000622886 0x1da6b8000731c4ff 0x63b4d70000e6389f

def z534 : W := mkw 0x2028ec000a390000 0xc4051d8001472000 0x0000b80000300000 0x0000170000060000

def z535 : W := mkw 0x10200a0016d58000 0x0204014002dab000 0x0020000007c18001 0x0004000000f83000

def z536 : W := mkw 0x3028ee000a7d8000 0xc6051dc0014fb000 0x1da6fe00073f8003 0x63b4dfc000e7f000

def z537 : W := mkw 0x18372fb017d5d600 0x6306e5f602fabac0 0x14273e3007c18701 0x0284e7c600f830e0

def z538 : W := mkw 0xe03ffdfedeb90000 0xfc07ffbfdbd72000 0xffbfffffff300000 0x5ff7ffffffe60000

def z539 : W := mkw 0x001701b000000000 0x2002e03600000000 0x0407003000000000 0x0080e00600000000

def z540 : W := mkw 0xf03ffffeca7d8000 0xfe07ffffd94fb000 0xff9fffffe03f8002 0x1ff3fffffc07f000

def z541 : W := mkw 0x151703b12046a18a 0x22a2e0762408d431 0xffdf47f3e0cfa79f 0xbffbe8fe7c19f4f3

def z542 : W := mkw 0x1d0203212146e58a 0x23a040642428dcb1 0xffe74733e7cfe79f 0xfffce8e67cf9fcf3

def z543 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xe0400033e0cfa79f 0xbc0800067c19f4f3

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec1003080c1a79f 0xbfd82006101834f3

def z545 : W := mkw 0x17001a05a257a1be 0x02e00340b44af437 0xfec1fe3fe0ffa7ff 0xbfd83fc7fc1ff4ff

def z546 : W := mkw 0x001ff52480000000 0xe003fea490000000 0xbf9fff2c80000000 0x17f3ffe590000000

def z547 : W := mkw 0xc00af56ec0000000 0xf8015eadd8000000 0xbd86ff2fe0000000 0x17b0dfe5fc000000

def z548 : W := mkw 0xa40ad16f882a28c0 0xb4815a2df1054518 0xffdef9ef983e78e6 0xfffbdf3df307cf1c

def z549 : W := mkw 0x0a1709b017915634 0x2142e13602f22ac6 0x67ff01f01ff1ffff 0xecffe03e03fe3fff

def z550 : W := mkw 0x1000020000448000 0x0200004000089000 0x18004600000f8002 0x030008c00001f000

def z551 : W := mkw 0x0a02112481004434 0x2140422490200886 0x0000002080000418 0x0000000410000083

def z552 : W := mkw 0x0002112480000000 0x2000422490000000 0xbd86b92c8001849f 0x37b0d72590003093

def z553 : W := mkw 0xac0ac16b092a6cc0 0xb581582d61254d98 0xeffec1ef1f3e7ce7 0xfdffd83de3e7cf9c

def z554 : W := mkw 0x3028ee000a7d8000 0xc6051dc0014fb000 0x1e81fe0000ff8003 0xa3d03fc0001ff000

def z555 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x98404603e0cfa79f 0xb30808c07c19f4f3

def z556 : W := mkw 0x0a1719b497915634 0x2142e33692f22ac6 0xbdbeb9ec9f31dcff 0x77b7d73d93e63b9f

def z557 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x63d801f018007f04 0xec7b003e03000fe0

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0x6681003000000000 0x0cd0200600000000

def z559 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x8840c00f183e78e6 0xf1081801e307cf1c

def z560 : W := mkw 0x0a02192497915634 0x2140432492f22ac6 0xbde6b92c9ff1ffff 0xf7bcd72593fe3fff

def z561 : W := mkw 0xc51ff5ffe002218a 0xf8a3febffc004431 0xffdfffffe000279c 0x1ffbfffffc0004f3

def z562 : W := mkw 0x080201b015805600 0x2100403602b00ac0 0x606001f01fc07f05 0xec0c003e03f80fe0

def z563 : W := mkw 0x050000012002218a 0x00a0000024004431 0x80000003e0000098 0x100000007c000013

def z564 : W := mkw 0xd51ff7ffe046a18a 0xfaa3fefffc08d431 0xff9fffffe00f809a 0x1ff3fffffc01f013

def z565 : W := mkw 0x1d00020135c6f78a 0x03a0004026b8def1 0x006000001fcfff9f 0xe00c000003f9fff3

def z566 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x07bfb8001ff00001 0xe0f7f70003fe0000

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x604001c000007804 0x0c08003800000f00

def z568 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x65e601f007007f05 0x6cbcc03e00e00fe0

def z569 : W := mkw 0xc01de4da54801200 0xd803bc9b4a900240 0x425946d378c03b00 0x884b28da6f180760

def z570 : W := mkw 0x2408c001082a2080 0x8481180021054410 0xebd8c003183e2086 0xfd7b18006307c410

def z571 : W := mkw 0x3a3fff249ffdc434 0xe747ffe493ffb886 0x1fbfff0c1fffc063 0xe3f7ffe183fff80c

def z572 : W := mkw 0x001dec0002110000 0xc003bd8000422000 0x1fbffe0007318003 0x63f7ffc000e63000

def z573 : W := mkw 0xa008c04a08280840 0x9401180941050108 0x0b98c1cc183e5862 0xe17318398307cb0c

def z574 : W := mkw 0x0a00080003114434 0x0140010000622886 0x0020000007304060 0x4004000000e6080c

def z575 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x561f7ef3e0000000 0x0ac3efde7c000000

def z576 : W := mkw 0x110002002044810a 0x0220004004089021 0x10000600e0018018 0x020000c01c003003

def z577 : W := mkw 0x0802012001004400 0x2100402400200880 0xada6812c073044e7 0x75b4d02580e6089c

def z578 : W := mkw 0x2008c00008280000 0x8401180001050000 0x0118800018300000 0x4023100003060000

def z579 : W := mkw 0x0400000100022080 0x0080000020004410 0x88004003000e0082 0x110008006001c010

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x0401003000c00701 0x00802006001800e0

def z581 : W := mkw 0x0015009014801200 0x0002a01202900240 0x0001001000c00300 0x0000200200180060

def z582 : W := mkw 0x8400004b000228c0 0x1080000960004518 0x404000c300003800 0x0808001860000700

def z583 : W := mkw 0xf53ffffffeffa18a 0xfea7ffffffdff431 0xffffffffffffa79f 0xfffffffffffff4f3

def z584 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xf4410633e0c1a79d 0x1e8820c67c1834f3

def z585 : W := mkw 0x001701b014800000 0x2002e03602900000 0x67bf01f01fc00001 0xecf7e03e03f80000

def z586 : W := mkw 0x303de6001cec8000 0xc607bcc0039d9000 0x07bf46001fce0001 0xe0f7e8c003f9c000

def z587 : W := mkw 0x2008c00008280000 0x8401180001050000 0x02184000180e0000 0x804308000301c000

def z588 : W := mkw 0xa008c04a08280840 0x9401180941050108 0x0000800c00300060 0x000010018006000c

def z589 : W := mkw 0x283fedb01fb95600 0xe507fdb603f72ac0 0x67ffb9f01ff07f05 0xecfff73e03fe0fe0

def z590 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x153fbe001ff18001 0x42a7f7c003fe3000

def z591 : W := mkw 0x15000a012257a18a 0x02a00140244af431 0xffe7fe33e7ffa79f 0xfffcffc67cfff4f3

def z592 : W := mkw 0x0002192482110000 0x2000432490422000 0xbda6b92c87318003 0x77b4d72590e63000

def z593 : W := mkw 0x000201b000000000 0x2000403600000000 0x600001f000000000 0x0c00003e00000000

def z594 : W := mkw 0x17001a05a257a1be 0x02e00340b44af437 0x9800fe0fe03f80fa 0x13001fc1fc07f01f

def z595 : W := mkw 0x0d0201b12102778a 0x21a0403624204ef1 0xe04001f3e0007f9c 0x1c08003e7c000ff3

def z596 : W := mkw 0x0202192482110034 0x2040432490422006 0xbd86b92c803180fa 0x17b0d7259006301f

def z597 : W := mkw 0x4015249040000000 0x4802a49208000000 0x0001061060000000 0x000020c20c000000

def z598 : W := mkw 0x0e021925831364b4 0x21c04324b0626c96 0xffe6f92f873fe4ff 0xfffcdf25f0e7fc9f

def z599 : W := mkw 0x3008c200086c8000 0x86011840010d9000 0x1f99c60018ff8003 0xe3f338c0031ff000

def z600 : W := mkw 0x0a17192497914434 0x2142e32492f22886 0xbfbfb92c9ff1c4ff 0xf7f7f72593fe389f

def z601 : W := mkw 0x303fefb01efd8000 0xe607fdf603dfb000 0x7fbffff01fff8003 0xeff7fffe03fff000

def z602 : W := mkw 0x1000020000448000 0x0200004000089000 0xfe814633e0cf8003 0xbfd028c67c19f000

def z603 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x00004003000e0000 0x000008006001c000

def z604 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x679fb9fc00000000 0x0cf3f73f80000000

def z605 : W := mkw 0x0802012015805600 0x2100402402b00ac0 0x25e601201fc07f05 0xe4bcc02403f80fe0

def z606 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x9e814603e0cf809b 0xb3d028c07c19f013

def z607 : W := mkw 0xd01ff7fec0448000 0xfa03feffd8089000 0xff9fffffe0cf8003 0xbff3fffffc19f000

def z608 : W := mkw 0x202008001eb90000 0x0404010003d72000 0x002000001f300000 0x4004000003e60000

def z609 : W := mkw 0xa008c04a08280000 0x9401180941050000 0xeb98c1cf183e0002 0xfd731839e307c000

def z610 : W := mkw 0x2a3ffd249fb94434 0xe547ffa493f72886 0x013eb90c1f304060 0x4027d72183e6080c

def z611 : W := mkw 0x35000201286ea9ca 0x06a00040250dd539 0x0040000018ffffff 0xe0080000031fffff

def z612 : W := mkw 0xa41dc04b1caa28c0 0x9483b80963954518 0xefffc1cf1ffe78e7 0xfdfff839e3ffcf1c

def z613 : W := mkw 0x303de6001cec8000 0xc607bcc0039d9000 0x1f9ffe0018ce0000 0x83f3ffc00319c000

def z614 : W := mkw 0x0000080002110000 0x0000010000422000 0x1800b80000318002 0x0300170000063000

def z615 : W := mkw 0x0000000000000000 0x0000000000000000 0x0980800000300002 0x6130100000060000

def z616 : W := mkw 0x081fe5b015805600 0xe103fcb602b00ac0 0x7ffffff01fc07f05 0xeffffffe03f80fe0

def z617 : W := mkw 0x303de6901cec9200 0xc607bcd2039d9240 0x425946d018ce3b00 0x884b28da0319c760

def z618 : W := mkw 0xc208fc4ec2110034 0xd8411f89d8422006 0x9800fe0fe03180fa 0x13001fc1fc06301f

def z619 : W := mkw 0x1b021b24a355c53e 0x23604364946ab8a7 0xbda7bf3ce7f1c7ff 0x77b4f7e79cfe38ff

def z620 : W := mkw 0x1015020014c48000 0x0202a04002989000 0x1fbf46001fcf8003 0xe3f7e8c003f9f000

def z621 : W := mkw 0x2008c00008280000 0x8401180001050000 0x6bd8c1c0183e7806 0xed7b18380307cf00

def z622 : W := mkw 0x35000201286ea9ca 0x06a00040250dd539 0xfec14633f8ffffff 0xffd828c67f1fffff

def z623 : W := mkw 0x24000001082a28c0 0x0480000021054518 0xa9c0810c183e78e6 0xf53810218307cf1c

def z624 : W := mkw 0x181703b015c4d600 0x2302e07602b89ac0 0x7fff47f01fcfff07 0xefffe8fe03f9ffe0

def z625 : W := mkw 0x8008c04a00000000 0x9001180940000000 0x011881cc00000000 0x0023103980000000

def z626 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x14410630e0cfa79f 0xa28820c61c19f4f3

def z627 : W := mkw 0x353de6013ceea18a 0xc6a7bcc0279dd431 0xfed94633f8cfa79f 0xbfdb28c67f19f4f3

def z628 : W := mkw 0xaa0ad96e8b394c74 0xb5415b2dd167298e 0xbdbeb9ec9f31dcff 0x77b7d73d93e63b9f

def z629 : W := mkw 0x0015009000000000 0x0002a01200000000 0x421900d000000000 0x0843201a00000000

def z630 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x66c1463360ce2705 0xacd828c66c19c4e0

def z631 : W := mkw 0xca0afd6ec3114434 0xf9415fadd8622886 0xbda6ff2fe731c4ff 0x77b4dfe5fce6389f

def z632 : W := mkw 0x343dee011effa080 0xc687bdc023dff410 0xfffffe031fffa087 0xffffffc063fff410

def z633 : W := mkw 0x511737b4e044810a 0x6a22e6f69c089021 0x14073e30e0c18719 0x0280e7c61c1830e3

def z634 : W := mkw 0x0200180482110034 0x0040030090422006 0xbc80b82c803184ff 0x379017059006309f

def z635 : W := mkw 0x8008c04a00000000 0x9001180940000000 0xff99c7ffe0000000 0x1ff338fffc000000

def z636 : W := mkw 0x30200a001efd8000 0x0604014003dfb000 0x1ea146001fff8003 0xe3d428c003fff000

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814633e001849f 0x3fd028c67c003093

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc80002080000000 0x1790000410000000

def z639 : W := mkw 0x0000080002110000 0x0000010000422000 0x1426380007018001 0x0284c70000e03000

def z640 : W := mkw 0xca1ffdfec3114434 0xf943ffbfd8622886 0x013eb9cc07304060 0x4027d73980e6080c

def z641 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xa980c10f003e40e6 0x75301821e007c81c

def z642 : W := mkw 0x283fedb01fb95600 0xe507fdb603f72ac0 0x013eb9c01f305800 0x4027d73803e60b00

def z643 : W := mkw 0x0a02112481004434 0x2140422490200886 0x0000010c00004060 0x000000218000080c

def z644 : W := mkw 0x1a373f2497d5c434 0x6346e7e492fab886 0x14273e2087c18419 0x0284e7c410f83083

def z645 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd8c1cf180e3800 0x9d7b1839e301c700

def z646 : W := mkw 0x1000020000448000 0x0200004000089000 0x0000000000cf8003 0xa00000000019f000

def z647 : W := mkw 0x0c1701b115827680 0x2182e03622b04ed0 0xefff41f31fce7f87 0xfdffe83e63f9cff0

def z648 : W := mkw 0xa81fc1fa1da85e40 0xb503f83f43b50bc8 0x67ff81fc1ff07f65 0xecfff03f83fe0fec

def z649 : W := mkw 0x2a3ffd249fb94434 0xe547ffa493f72886 0xbdbeb92c9f31c4ff 0x77b7d72593e6389f

def z650 : W := mkw 0x34200a011effa8c0 0x0684014023dff518 0x006000001ffff8e7 0xe00c000003ffff1c

def z651 : W := mkw 0x0a1719b497915634 0x2142e33692f22ac6 0x013eb9cc1f305860 0x4027d73983e60b0c

def z652 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x991effcfe0000000 0x1323dff9fc000000

def z653 : W := mkw 0x0800000001005600 0x0100000000200ac0 0x0040000000007f04 0x0008000000000fe0

def z654 : W := mkw 0x0802012001004400 0x2100402400200880 0x67fe01e01f007c05 0xecffc03c03e00f80

def z655 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x63fe01c01f007804 0xec7fc03803e00f00

def z656 : W := mkw 0x0200100480000034 0x0040020090000006 0x8000000c800000f8 0x100000019000001f

def z657 : W := mkw 0xa408c84b0a3b28c0 0x9481190961476518 0xfffef9cf1f3ff8e7 0xffffdf39e3e7ff1c

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000010c000040e4 0x140000218000081c

def z659 : W := mkw 0x0f021925a31365be 0x21e04324b4626cb7 0xfde6b93fe731e7ff 0x7fbcd727fce63cff

def z660 : W := mkw 0x3f3fff25bfffe5be 0xe7e7ffe4b7fffcb7 0xffffff3fffffe7ff 0xffffffe7fffffcff

def z661 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0xeb99c7df60000000 0x1d7338fbec000000

def z662 : W := mkw 0xd50213ffe046a18a 0x3aa0427ffc08d431 0xfec147ffe0cfa79f 0xbfd828fffc19f4f3

def z663 : W := mkw 0x050000012002218a 0x00a0000024004431 0xe6c10033e0c0279d 0xbcd820067c1804f3

def z664 : W := mkw 0x1f171bb5b7d7f7be 0x23e2e376b6fafef7 0xffffffffffffffff 0xffffffffffffffff

def z665 : W := mkw 0x0200180482110034 0x0040030090422006 0xb980b90c8031c0fe 0x773017219006381f

def z666 : W := mkw 0xac08c04b1daa7ec0 0x9581180963b54fd8 0xebf8c1cf1ffe7fe7 0xfd7f1839e3ffcffc

def z667 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x617e01f01f007f04 0x4c2fc03e03e00fe0

def z668 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xca58c0cf183e38e2 0x994b1819e307c71c

def z669 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x07bf01c01fc05801 0xe0f7e03803f80b00

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000033e0000000 0x1c0000067c000000

def z671 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x1f9fffcc00000000 0x03f3fff980000000

def z672 : W := mkw 0xb428ee4b0a7fa8c0 0xd6851dc9614ff518 0x9800fe0f003f80e2 0x13001fc1e007f01c

def z673 : W := mkw 0x0a02192483114434 0x2140432490622886 0x35a639208701c41d 0x66b4c72410e03883

def z674 : W := mkw 0x0a02112481004434 0x2140422490200886 0xa980812c803044fe 0x753010259006089f

def z675 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x5ec1461360cfa303 0xabd828c26c19f460

def z676 : W := mkw 0x0015000014800000 0x0002a00002900000 0x0219000018c00000 0x8043200003180000

def z677 : W := mkw 0xb43dee4b1effa8c0 0xd687bdc963dff518 0x5ffffec31fffb803 0xebffffd863fff700

def z678 : W := mkw 0x0d1701b13582778a 0x21a2e03626b04ef1 0xe7ff01f3ffc07f9d 0xfcffe03e7ff80ff3

def z679 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0x001800c000000000 0x0003001800000000

def z680 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x07bf00301fc00701 0xe0f7e00603f800e0

def z681 : W := mkw 0x0a00080003114434 0x0140010000622886 0xbca000208731c4ff 0x7794000410e6389f

def z682 : W := mkw 0x0a1719b483114434 0x2142e33690622886 0xffbfb9fc8731c4ff 0x7ff7f73f90e6389f

def z683 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xeac0c00f003e20e6 0xbd581801e007c41c

def z684 : W := mkw 0x0015000000000000 0x0002a00000000000 0x079f000000000000 0x00f3e00000000000

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x4201461360000000 0x084028c26c000000

def z686 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xe25841cf180e78e4 0x9c4b0839e301cf1c

def z687 : W := mkw 0x0015000014800000 0x0002a00002900000 0x0427000007c00001 0x0084e00000f80000

def z688 : W := mkw 0x0a02192483114434 0x2140432490622886 0xa126b92c873044fc 0x5424d72590e6089f

def z689 : W := mkw 0x0400000100022080 0x0080000020004410 0xeec1403300ce2787 0xbdd828066019c4f0

def z690 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0x67ffb9fc1fc07f05 0xecfff73f83f80fe0

def z691 : W := mkw 0x343dee011effa8c0 0xc687bdc023dff518 0x1ffffe001ffff8e7 0xe3ffffc003ffff1c

def z692 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xe21947ffe0000000 0x1c4328fffc000000

def z693 : W := mkw 0x303dee000a7d8000 0xc607bdc0014fb000 0x1f9ffe00003f8002 0x03f3ffc00007f000

def z694 : W := mkw 0x1000020000448000 0x0200004000089000 0x1401060000c18001 0x028020c000183000

def z695 : W := mkw 0xc00211fec0000000 0x3800423fd8000000 0xfe8147ffe0000000 0x1fd028fffc000000

def z696 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbda6b92c87018419 0x17b4d72590e03083

def z697 : W := mkw 0x0a1719b497915634 0x2142e33692f22ac6 0x1427383087c18719 0x0284e70610f830e3

def z698 : W := mkw 0x1d1703b135c6f78a 0x23a2e07626b8def1 0x67ff47f37fce7f05 0xecffe8fe6ff9cfe0

def z699 : W := mkw 0x401ff5b4c0000000 0xe803feb698000000 0x1f9ffe30e0000000 0x03f3ffc61c000000

def z700 : W := mkw 0xc01fe5fa40000000 0xf803fcbf48000000 0x679f47f360000000 0x0cf3e8fe6c000000

def z701 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xbd9eb9ec80000000 0x17b3d73d90000000

def z702 : W := mkw 0xa41de44b082a28c0 0xd483bc8961054518 0xffdfffcf183e78e6 0xfffbfff9e307cf1c

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0xebd881cc183078e6 0xfd7b103983060f1c

def z704 : W := mkw 0x1a021b248355c434 0x23404364906ab886 0xbfa7ff2c87ffc4ff 0xf7f4ffe590fff89f

def z705 : W := mkw 0x3a3fffb49ffdd634 0xe747fff693ffbac6 0xfffffffc9fffffff 0xffffffff93ffffff

def z706 : W := mkw 0x9500024b2046a9ca 0x12a000496408d539 0xfec147ffe0cfffff 0xbfd828fffc19ffff

def z707 : W := mkw 0xf03deeda5efd9200 0xde07bddb4bdfb240 0x5ffffed37fffbb03 0xebffffda6ffff760

def z708 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x6fff41f01fce7f07 0xedffe83e03f9cfe0

def z709 : W := mkw 0x001711b480000000 0x2002e23690000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z710 : W := mkw 0x1f000a012357e5be 0x03e00140246afcb7 0x00200000073fc4ff 0x6004000000e7f89f

def z711 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xfbd8c7cff83e78e6 0xff7b18f9ff07cf1c

def z712 : W := mkw 0xe01ff5fec8280840 0xfc03febfd9050108 0xff9ffffff8001800 0x1ff3ffffff000300

def z713 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x9d86fe0fe0000000 0x13b0dfc1fc000000

def z714 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xe31fffffe0000000 0x1c63fffffc000000

def z715 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdfffffe0002704 0x1ffbfffffc0004e0

def z716 : W := mkw 0xe01ff5fec8280000 0xfc03febfd9050000 0xff9ffffff80e0000 0x9ff3ffffff01c000

def z717 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd9c1df18fe7be6 0xfd7b383be31fcf7c

def z718 : W := mkw 0xd51ff7ffe046a18a 0xfaa3fefffc08d431 0x015eb9cc00cfa79f 0xa02bd7398019f4f3

def z719 : W := mkw 0x0002112480000000 0x2000422490000000 0xbd86ff2fe0000000 0x17b0dfe5fc000000

def z720 : W := mkw 0x35200a012a7fa18a 0x06a40140254ff431 0x0040000000ffa79f 0xa0080000001ff4f3

def z721 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xefff01f01fc07f87 0xfdffe03e03f80ff0

def z722 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x013eb8001ffe0000 0xc027d70003ffc000

def z723 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffffffffff007f04 0x5fffffffffe00fe0

def z724 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x5ffffec01fffb803 0xebffffd803fff700

def z725 : W := mkw 0xc00af56ec0000000 0xf8015eadd8000000 0x9906ff0fe0000000 0x1320dfe1fc000000

def z726 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xbfbfff0c1fff8003 0xf7f7ffe183fff000

def z727 : W := mkw 0x253dec013ebb218a 0xc4a7bd8027d76431 0xe17eb833ff30279c 0x5c2fd7067fe604f3

def z728 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x017801c01fc07f05 0xe02f003803f80fe0

def z729 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0x993effcfff005800 0x5327dff9ffe00b00

def z730 : W := mkw 0x303dee901efd9200 0xc607bdd203dfb240 0x7fffffd01ffffb07 0xeffffffa03ffff60

def z731 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x467f00f01fc07f05 0xe8cfe01e03f80fe0

def z732 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfec147f3e0cfff9f 0xbfd828fe7c19fff3

def z733 : W := mkw 0x3028ee001efd8000 0xc6051dc003dfb000 0x1da6fe001fff8003 0xe3b4dfc003fff000

def z734 : W := mkw 0xa008c04a08280840 0x9401180941050108 0x6bd8c1cc183e7866 0xed7b18398307cf0c

def z735 : W := mkw 0x0a02192483114434 0x2140432490622886 0x25a6b92c0731c4ff 0x64b4d72580e6389f

def z736 : W := mkw 0x150002012046a9ca 0x02a000402408d539 0xfec14633e0cfffff 0xbfd828c67c19ffff

def z737 : W := mkw 0xc01ff5fed4801200 0xf803febfda900240 0xff9fffffe0c00300 0x1ff3fffffc180060

def z738 : W := mkw 0xe01ff5fec8280000 0xfc03febfd9050000 0xffdffffff83e7806 0xfffbffffff07cf00

def z739 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x10007e03e0000000 0x02000fc07c000000

def z740 : W := mkw 0x3a3ff7249decc434 0xe747fee493bd9886 0xa219472c98ce44fc 0x944328e59319c89f

def z741 : W := mkw 0xc01ff5fed4801200 0xf803febfda900240 0xffffffffffc03b01 0xfffffffffff80760

def z742 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffffffffffc03f01 0x9ffffffffff807e0

def z743 : W := mkw 0xc01df44ec0000000 0xd803be89d8000000 0x991efe0fe0000000 0x1323dfc1fc000000

def z744 : W := mkw 0x201dec000a390000 0xc403bd8001472000 0x1fbffe001f3f8003 0xe3f7ffc003e7f000

def z745 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x421f7ed360000000 0x0843efda6c000000

def z746 : W := mkw 0x323dee001efd8034 0xc647bdc003dfb006 0x1fbffe001fff80fb 0xe3f7ffc003fff01f

def z747 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffc1c73fe0cfa79f 0xbff838e7fc19f4f3

def z748 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xb980ff0fe0000000 0x17301fe1fc000000

def z749 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x66ff00f01fc03f05 0xacdfe01e03f807e0

def z750 : W := mkw 0x94352e4b16d7a8c0 0x5286a5c962daf518 0xf4673fcf07c1f8e5 0x1e8ce7f9e0f83f1c

def z751 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x14014633e0cf8719 0x028028c67c19f0e3

def z752 : W := mkw 0xc00af56ec0000000 0xf8015eadd8000000 0xff9effefe0000000 0x1ff3dffdfc000000

def z753 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xfe87fe3fe0000000 0x1fd0ffc7fc000000

def z754 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x7fbfffc01fff8003 0xeff7fff803fff000

def z755 : W := mkw 0xac1fc1fb1daa7ec0 0xb583f83f63b54fd8 0x8c27c03f07fe07e3 0x1184f807e0ffc0fc

def z756 : W := mkw 0xe03ff5fedca80000 0xfc07febfdb950000 0xff9ffffff8000000 0x1ff3ffffff000000

def z757 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xeb9fffdf60000000 0x1d73fffbec000000

def z758 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfec1473fe0cfe7ff 0xbfd828e7fc19fcff

def z759 : W := mkw 0xe008f44ec8280840 0xdc011e89d9050108 0x9918ffcff8305860 0x53231ff9ff060b0c

def z760 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x0bbef8001fff8003 0xe177df0003fff000

def z761 : W := mkw 0x0a02192483114434 0x2140432490622886 0x0126b90c0731c0fa 0x4024d72180e6381f

def z762 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xe25841cf183e78e6 0xfc4b0839e307cf1c

def z763 : W := mkw 0x0a02192483114434 0x2140432490622886 0xa9a6b90c0731c4ff 0x7534d72180e6389f

def z764 : W := mkw 0x0a02192483114434 0x2140432490622886 0x9826b80c873180fa 0x1304d70190e6301f

def z765 : W := mkw 0x0a0219b483115634 0x2140433690622ac6 0xfffeb9fc9f31ffff 0xffffd73f93e63fff

def z766 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xda01fe1fe0000000 0x1b403fc3fc000000

def z767 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfed946f3f8cfbf9f 0xbfdb28de7f19f7f3

def z768 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffffffffffc07b00 0xdffffffffff80f60

def z769 : W := mkw 0x313dee003efd810a 0xc627bdc007dfb021 0x1fbffe001fff871b 0xe3f7ffc003fff0e3

def z770 : W := mkw 0x0f021125a10265be 0x21e04224b4204cb7 0xa000012fe00044fc 0x14000025fc00089f

def z771 : W := mkw 0xa400004b082a28c0 0x1480000961054518 0xe3d801cf183e78e6 0xfc7b0039e307cf1c

def z772 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x0bd8c1cc183e78e6 0xe17b18398307cf1c

def z773 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x5f9fffdf60000000 0x0bf3fffbec000000

def z774 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x9d1fffffe0000000 0x13a3fffffc000000

def z775 : W := mkw 0x1f021b25a357e5be 0x23e04364b46afcb7 0x4367ff1f67fe6360 0xc86cffe3ecffcc6c

def z776 : W := mkw 0xc80af56ec1004400 0xf9015eadd8200880 0xbda6ff2fe7004405 0x77b4dfe5fce00880

def z777 : W := mkw 0xca0af56ec1004434 0xf9415eadd8200886 0xb800ff2fe00044fc 0x17001fe5fc00089f

def z778 : W := mkw 0xc01ff56ec0000000 0xf803feadd8000000 0xbf9fff2fe0000000 0x17f3ffe5fc000000

def z779 : W := mkw 0x382aefb00b7dd600 0xe7055df6016fbac0 0x7840fff0003fff06 0x0f081ffe0007ffe0

def z780 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0300002 0x7ff3fffffc060000

def z781 : W := mkw 0xc01ff5fed4800000 0xf803febfda900000 0xffbfffffe7c00001 0x1ff7fffffcf80000

def z782 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xffbffe33ffff849f 0xfff7ffc67ffff093

def z783 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xe7ff01f09fc07f9d 0xfcffe03e13f80ff3

def z784 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff01f01fc07b00 0xccffe03e03f80f60

def z785 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xe7ff01fc1fc07fe5 0xfcffe03f83f80ffc

def z786 : W := mkw 0x2008c00008280000 0x8401180001050000 0xebd8c1cc183e78e6 0xfd7b18398307cf1c

def z787 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x07bfb8001fff8003 0xe0f7f70003fff000

def z788 : W := mkw 0x0a1701b015805634 0x2142e03602b00ac6 0x67ff01f01fc07ffd 0xecffe03e03f80fff

def z789 : W := mkw 0x641735b5c82a28c0 0x6c82e6b6b9054518 0x14473e30f83e78e6 0xe288e7c61f07cf1c

def z790 : W := mkw 0xcf0211ffe10265be 0x39e0423ffc204cb7 0xe04001ffe00067fc 0x1c08003ffc000cff

def z791 : W := mkw 0x0a02192483114434 0x2140432490622886 0xfde6b9ec8731fcff 0x7fbcd73d90e63f9f

def z792 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0xffffffffffc07f05 0xfffffffffff80fe0

def z793 : W := mkw 0x15021325a046a18a 0x22a04264b408d431 0xbdc6b92c80cfa79f 0xb7b8d7259019f4f3

def z794 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbde6b92c9f31fcff 0xf7bcd72593e63f9f

def z795 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x163f7e001fff8003 0xe2c7efc003fff000

def z796 : W := mkw 0xe008f44ec8280840 0xdc011e89d9050108 0x9800fe0fe0300060 0x13001fc1fc06000c

def z797 : W := mkw 0x1b171bb4b7d5d73e 0x2362e37696fabae7 0x14273e30e7c18719 0x0284e7c61cf830e3

def z798 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x63ff01d01fc07b04 0xec7fe03a03f80f60

def z799 : W := mkw 0x050008012213218a 0x00a0010024426431 0xfde6b833e731a79f 0x7fbcd7067ce634f3

def z800 : W := mkw 0x30352e001efd8000 0x4606a5c003dfb000 0x17bf3e001fff8003 0xe2f7e7c003fff000

def z801 : W := mkw 0xc01ff5fed4800000 0xf803febfda900000 0xffffffffffc07805 0xfffffffffff80f00

def z802 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x63d881cc183e78e6 0xec7b10398307cf1c

def z803 : W := mkw 0x0a02192483115634 0x2140432490622ac6 0xbde6b92c8731ffff 0x77bcd72590e63fff

def z804 : W := mkw 0xf0221bfedefd8000 0x3e04437fdbdfb000 0xe02001ffffff8003 0xfc04003ffffff000

def z805 : W := mkw 0x30200a000a7d8000 0x06040140014fb000 0x1da6b800073f8003 0x63b4d70000e7f000

def z806 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0004004 0x7ff3fffffc000800

def z807 : W := mkw 0xc808f44ed5805600 0xd9011e89dab00ac0 0x9860fe0fffc07f05 0xf30c1fc1fff80fe0

def z808 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd8c1cf183ffcff 0xfd7b1839e307ff9f

def z809 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff01f01ff07fe7 0xecffe03e03fe0ffc

def z810 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0x77ff7ff3ffc07f05 0xeeffeffe7ff80fe0

def z811 : W := mkw 0x0200180482110034 0x0040030090422006 0x9926b80c873180fa 0x5324d70190e6301f

def z812 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x63fe01c01fc07f05 0xec7fc03803f80fe0

def z813 : W := mkw 0x3028ee000a7d8000 0xc6051dc0014fb000 0x1fa7fe0007ff8003 0xe3f4ffc000fff000

def z814 : W := mkw 0x200008000a390000 0x0400010001472000 0x1da6b8001f3f8003 0xe3b4d70003e7f000

def z815 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xefff41f31fc07f05 0xfdffe83e63f80fe0

def z816 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xeb98c1cf183e58e2 0x5d731839e307cb1c

def z817 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x7ffffff01fffff07 0xeffffffe03ffffe0

def z818 : W := mkw 0x0200180482110034 0x0040030090422006 0x9c26b80c873180fb 0x1384d70190e6301f

def z819 : W := mkw 0x800ad16e80000000 0xb0015a2dd0000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z820 : W := mkw 0xc01ff5fec0000840 0xf803febfd8000108 0xff9fffffe0005860 0x1ff3fffffc000b0c

def z821 : W := mkw 0xc00af56ec0000000 0xf8015eadd8000000 0x9c06fe2fe0000000 0x1380dfc5fc000000

def z822 : W := mkw 0x0a1711b495805634 0x2142e23692b00ac6 0x67ff01fc1fc07f65 0xecffe03f83f80fec

def z823 : W := mkw 0x081fe5b015805600 0xe103fcb602b00ac0 0xfffffff3ffc07f05 0xfffffffe7ff80fe0

def z824 : W := mkw 0x0f021125a10265be 0x21e04224b4204cb7 0xa040012c800067fc 0x1408002590000cff

def z825 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x571fffffe0000000 0x0ae3fffffc000000

def z826 : W := mkw 0x10000a0002558000 0x02000140004ab000 0x1da6b80007ff8003 0xe3b4d70000fff000

def z827 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbfa7ff2c8731c4ff 0x77f4ffe590e6389f

def z828 : W := mkw 0xe01ff5fedca80000 0xfc03febfdb950000 0xffbffffffffe0003 0xfff7ffffffffc000

def z829 : W := mkw 0x40003404c0000000 0x4800068098000000 0x98007e03e0000000 0x13000fc07c000000

def z830 : W := mkw 0xc01ff5fed4800000 0xf803febfda900000 0xffffffffffc02705 0xfffffffffff804e0

def z831 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffe74633e7cfa79f 0xfffce8c67cf9f4f3

def z832 : W := mkw 0xb03dee4a1efd8000 0xd607bdc943dfb000 0x9fbffe0f1fff8003 0xf3f7ffc1e3fff000

def z833 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xffd9c7cf183e78e6 0xfffb38f9e307cf1c

def z834 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xdb1fffdfe0000000 0x1b63fffbfc000000

def z835 : W := mkw 0x0a02192483114434 0x2140432490622886 0xfde6b93c8731e7ff 0x7fbcd72790e63cff

def z836 : W := mkw 0x1d1703b135c6f78a 0x23a2e07626b8def1 0x993e47c3ff0fd89a 0x5327c8f87fe1fb13

def z837 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x9fbffe0c1fff80e3 0xf3f7ffc183fff01c

def z838 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffbfffffe7000000 0x1ff7fffffce00000

def z839 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0000405 0x3ff3fffffc000080

def z840 : W := mkw 0x201dc8001eb90000 0x8403b90003d72000 0x1fbff8001fff8003 0xe3f7ff0003fff000

def z841 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0xffff7ff3ffc07f05 0xffffeffe7ff80fe0

def z842 : W := mkw 0x0a1711b495805634 0x2142e23692b00ac6 0xffffb9fc9fc07ffd 0xfffff73f93f80fff

def z843 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffffffffffc1ff9f 0xfffffffffff83ff3

def z844 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xbc80fe2fe0000000 0x17901fc5fc000000

def z845 : W := mkw 0xb03dee4a1efd8840 0xd607bdc943dfb108 0x1fbffec01fff9803 0xe3f7ffd803fff300

def z846 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x63f901d01fc07f05 0xec7f203a03f80fe0

def z847 : W := mkw 0xa008c04a08280840 0x9401180941050108 0x0318c1cc183e5860 0xc06318398307cb0c

def z848 : W := mkw 0xa508c04b282a29ca 0x94a1180965054539 0xffd9c7fff83e7ffe 0xfffb38ffff07cfff

def z849 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1e3ffe001fff8003 0x83c7ffc003fff000

def z850 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x193efe001fff8003 0xe327dfc003fff000

def z851 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff47f37fc07f05 0xecffe8fe6ff80fe0

def z852 : W := mkw 0xc01df4dec0000000 0xd803be9bd8000000 0x52197ed3e0000000 0x0a432fda7c000000

def z853 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xff9f7ff3e0000000 0x1ff3effe7c000000

def z854 : W := mkw 0x0000100480000000 0x0000020090000000 0x9800fe0fe0000000 0x13001fc1fc000000

def z855 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xffdef9cf183e78e6 0xfffbdf39e307cf1c

def z856 : W := mkw 0xc01ff5fed4801200 0xf803febfda900240 0xffdffffff8c07b04 0xfffbffffff180f60

def z857 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdfffffe0002004 0xbffbfffffc000400

def z858 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x057f01f01fc07f05 0xe0afe03e03f80fe0

def z859 : W := mkw 0xc01df4dec0000000 0xd803be9bd8000000 0xfb99ffdfe0000000 0x1f733ffbfc000000

def z860 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbda7b93c87f1c7ff 0x77b4f72790fe38ff

def z861 : W := mkw 0x313dee003efd810a 0xc627bdc007dfb021 0x1fbffe107fff8303 0xe3f7ffc20ffff060

def z862 : W := mkw 0x0a02192483114434 0x2140432490622886 0xb526b92c8731c4fd 0x56a4d72590e6389f

def z863 : W := mkw 0xc00af56ec0000000 0xf8015eadd8000000 0xb800ff2fe0000000 0x17001fe5fc000000

def z864 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x9fbffe009fff809b 0xf3f7ffc013fff013

def z865 : W := mkw 0x0a02192483114434 0x2140432490622886 0x9c26b82c8731c4ff 0x7384d70590e6389f

def z866 : W := mkw 0xe408e44b482a28c0 0xdc811c8969054518 0xebd8c7cf783e78e6 0xfd7b18f9ef07cf1c

def z867 : W := mkw 0xe008f44ec8280000 0xdc011e89d9050000 0x9800fe0fe03e0002 0x13001fc1fc07c000

def z868 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x9c414633e0cfa79f 0xb38828c67c19f4f3

def z869 : W := mkw 0xc01ff5fed4800000 0xf803febfda900000 0xff9ffffff8c00000 0x9ff3ffffff180000

def z870 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xa9d881cc183e78e6 0xf53b10398307cf1c

def z871 : W := mkw 0x0a02192483114434 0x2140432490622886 0xffa7b93c8731c4ff 0x7ff4f72790e6389f

def z872 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd8c1ef983e7cfe 0xfd7b183df307cf9f

def z873 : W := mkw 0x101dee0002558000 0xc203bdc0004ab000 0x1fbffe0007ff8003 0xe3f7ffc000fff000

def z874 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x033ef8001f3e0000 0xc067df0003e7c000

def z875 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbc26b92c8731c4ff 0x1784d72590e6389f

def z876 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xeffec1cf1f3e78e7 0xfdffd839e3e7cf1c

def z877 : W := mkw 0x0e02112581026cf4 0x21c04224b0204d9e 0xa040012c80007cfc 0x1408002590000f9f

def z878 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xfffffe33ffffa707 0xffffffc67ffff4e0

def z879 : W := mkw 0x30200a001efd8000 0x0604014003dfb000 0x142638001fff8003 0xe284c70003fff000

def z880 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9ffffff8000000 0xfff3ffffff000000

def z881 : W := mkw 0xe01ff5fec8280840 0xfc03febfd9050108 0xff9ffffff83e5862 0xfff3ffffff07cb0c

def z882 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe0007ff8003 0x03f7ffc000fff000

def z883 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x153fbe001fff8003 0xe2a7f7c003fff000

def z884 : W := mkw 0x30350a001efd8000 0x0606a14003dfb000 0x1fbfb8001fff8003 0xe3f7f70003fff000

def z885 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x0000fe0f60000000 0x00001fc1ec000000

def z886 : W := mkw 0xc01ff5fed4801200 0xf803febfda900240 0xffdffffff8c03f05 0xbffbffffff1807e0

def z887 : W := mkw 0xc01735fec0000000 0x7802e6bfd8000000 0xfd87bfffe0000000 0x1fb0f7fffc000000

def z888 : W := mkw 0x303dee901efd9200 0xc607bdd203dfb240 0x1fbffe101fff8303 0xe3f7ffc203fff060

def z889 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x1fbffe001f3e0002 0xe3f7ffc003e7c000

def z890 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfec1c63fe0ffa7ff 0xbfd838c7fc1ff4ff

def z891 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbda7bf3ce731c4ff 0x77b4f7e79ce6389f

def z892 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x17bf7e001fcf8001 0xe2f7efc003f9f000

def z893 : W := mkw 0xc81ff5fec1005600 0xf903febfd8200ac0 0xffffffffe7007f05 0x7ffffffffce00fe0

def z894 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x76c14633e0cfa71d 0xaed828c67c19f4e3

def z895 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1d3ffe001fff8003 0x43a7ffc003fff000

def z896 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xfffffffffff07fe7 0xfffffffffffe0ffc

def z897 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x011881cc183e58e2 0x402310398307cb1c

def z898 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0c00701 0x1ff3fffffc1800e0

def z899 : W := mkw 0x481711b4d5805600 0x2902e2369ab00ac0 0x67ff01f0ffc07f05 0xecffe03e1ff80fe0

def z900 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x627901f01fc07f05 0xec4f203e03f80fe0

def z901 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xfec1fe3fe0c02705 0xbfd83fc7fc1804e0

def z902 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x7fff47f01fc07f05 0xefffe8fe03f80fe0

def z903 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffbfffffffc05f01 0x5ff7fffffff80be0

def z904 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffc14733e0cfe79f 0xfff828e67c19fcf3

def z905 : W := mkw 0x001701b014801200 0x2002e03602900240 0x67ff01f01fc03b01 0xecffe03e03f80760

def z906 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xfa80fe0fe0000000 0x1f501fc1fc000000

def z907 : W := mkw 0x0a00180483114434 0x0140030090622886 0x9da6b80c8731c4ff 0x73b4d70190e6389f

def z908 : W := mkw 0xa408e44b082a28c0 0xd4811c8961054518 0xfbd8ffcf183e78e6 0xff7b1ff9e307cf1c

def z909 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0x561f7ed360000000 0x0ac3efda6c000000

def z910 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdfffffe0c02300 0x9ffbfffffc180460

def z911 : W := mkw 0x0f0211b5a10277be 0x21e04236b4204ef7 0xe04001ffe0007ffc 0x1c08003ffc000fff

def z912 : W := mkw 0xc81735fed5805600 0x7902e6bfdab00ac0 0xf4673fffe7c07f05 0x1e8ce7fffcf80fe0

def z913 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x427900d01fc07b00 0xc84f201a03f80f60

def z914 : W := mkw 0x201de4001ca80000 0xc403bc8003950000 0x1fbffe001ffe0003 0xe3f7ffc003ffc000

def z915 : W := mkw 0xca1ff5fec1004434 0xf943febfd8200886 0xff9fffffe0004060 0x1ff3fffffc00080c

def z916 : W := mkw 0xc01df4dec0000000 0xd803be9bd8000000 0xdf9ffedfe0000000 0x1bf3ffdbfc000000

def z917 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0xff9fffdf60000000 0x1ff3fffbec000000

def z918 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdffffff8c07f05 0xfffbffffff180fe0

def z919 : W := mkw 0x303dee001efd8840 0xc607bdc003dfb108 0x1fbffe001fffd863 0xe3f7ffc003fffb0c

def z920 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xbd9effefe0000000 0x17b3dffdfc000000

def z921 : W := mkw 0xc81ff5fec1005600 0xf903febfd8200ac0 0xff9fffffe0005800 0x1ff3fffffc000b00

def z922 : W := mkw 0x3f200a013fffe5be 0x07e4014027fffcb7 0x006000001fffe7ff 0xe00c000003fffcff

def z923 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0x77ff39f09fc07f05 0xeeffe73e13f80fe0

def z924 : W := mkw 0x0a02192483114434 0x2140432490622886 0xffa6f92f8731c4ff 0x7ff4df25f0e6389f

def z925 : W := mkw 0x8400084b021328c0 0x1080010960426518 0xfde6b9cf0731f8e7 0x7fbcd739e0e63f1c

def z926 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x7fff01f01fc1ff07 0xefffe03e03f83fe0

def z927 : W := mkw 0x0a1711b495805634 0x2142e23692b00ac6 0xffff01fc9fc1ffff 0xffffe03f93f83fff

def z928 : W := mkw 0x0a02192483114434 0x2140432490622886 0x9da6b82c873184fb 0x73b4d70590e6309f

def z929 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x14277e0007cf8001 0x0284efc000f9f000

def z930 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0xffffb9fc9fc1ff9f 0xfffff73f93f83ff3

def z931 : W := mkw 0xcc0211ffc1027ec0 0x3980423ff8204fd8 0xe04001ffe0007fe4 0x1c08003ffc000ffc

def z932 : W := mkw 0xc01df4dec0000000 0xd803be9bd8000000 0x9801fe1fe0000000 0x13003fc3fc000000

def z933 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x9918ffcfe0000000 0x13231ff9fc000000

def z934 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe031c4ff 0x7ff3fffffc06389f

def z935 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xde1ffeffe0000000 0x1bc3ffdffc000000

def z936 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffd94633f8cfa79f 0xfffb28c67f19f4f3

def z937 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd8c1cf183e7860 0xdd7b1839e307cf0c

def z938 : W := mkw 0xc01735fec0000000 0x7802e6bfd8000000 0xf79f3fffe0000000 0x1ef3e7fffc000000

def z939 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x5f9ffef3e0000000 0x0bf3ffde7c000000

def z940 : W := mkw 0xc00af5fec0000000 0xf8015ebfd8000000 0xfe81ffffe0000000 0x1fd03ffffc000000

def z941 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbda6b92c873184fb 0x17b4d72590e6309f

def z942 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0x567f7ef3ffc03f01 0x8acfefde7ff807e0

def z943 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffbfffffff005c05 0x7ff7ffffffe00b80

def z944 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe001fcf8001 0x83f7ffc003f9f000

def z945 : W := mkw 0xa008c04a08280840 0x9401180941050108 0xeb98c1cf183e5862 0xfd731839e307cb0c

def z946 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff81fc1ff07f65 0xecfff03f83fe0fec

def z947 : W := mkw 0xce0211ffc1026cf4 0x39c0423ff8204d9e 0xe04001ffe0007cfc 0x1c08003ffc000f9f

def z948 : W := mkw 0xc01df4dec0000000 0xd803be9bd8000000 0xfe99feffe0000000 0x1fd33fdffc000000

def z949 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xefff81fc1fc07f05 0xfdfff03f83f80fe0

def z950 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffffffffff007804 0xffffffffffe00f00

def z951 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x5ec14633e0cfa71b 0xabd828c67c19f4e3

def z952 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffc1c633e0ffa79f 0xfff838c67c1ff4f3

def z953 : W := mkw 0xb108c24a286c894a 0x96211849450d9129 0x151987fcf8f1df79 0x42a330ff9f1e3bef

def z954 : W := mkw 0xc81ff5fec1005600 0xf903febfd8200ac0 0xff9fffffe0000700 0x1ff3fffffc0000e0

def z955 : W := mkw 0x313dee003efd810a 0xc627bdc007dfb021 0xffbffe33ffff871b 0xfff7ffc67ffff0e3

def z956 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x3fbffe201fff8407 0xe7f7ffc403fff080

def z957 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x011effcf60000000 0x0023dff9ec000000

def z958 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1dbefe001f3f8003 0x63b7dfc003e7f000

def z959 : W := mkw 0xcd0211ffe102778a 0x39a0423ffc204ef1 0xe04001ffe0007f9c 0x1c08003ffc000ff3

def z960 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfec14633e0ffe7ff 0xffd828c67c1ffcff

def z961 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbfff0c1fffc063 0xe3f7ffe183fff80c

def z962 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x0bbffe001ffe0002 0xe177ffc003ffc000

def z963 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xfa19ffffe0000000 0x1f433ffffc000000

def z964 : W := mkw 0xe81ff5fedda85e40 0xfd03febfdbb50bc8 0xfffffffffff07f65 0xfffffffffffe0fec

def z965 : W := mkw 0xc01735fec0000000 0x7802e6bfd8000000 0x54073ef3e0000000 0x0a80e7de7c000000

def z966 : W := mkw 0xc81ff5fec1004400 0xf903febfd8200880 0xffbfffffe7004000 0x5ff7fffffce00800

def z967 : W := mkw 0x0215189496911234 0x0042a31292d22246 0xda59b8dc98f1bbfa 0x9b4b371b931e377f

def z968 : W := mkw 0x303de6001cec8000 0xc607bcc0039d9000 0x1fbffe001fce0001 0xe3f7ffc003f9c000

def z969 : W := mkw 0x0200180482110034 0x0040030090422006 0xbda6b82c873184ff 0x77b4d70590e6309f

def z970 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x47ff00f01fc03f01 0xe8ffe01e03f807e0

def z971 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd8c1fff83e78e6 0xfd7b183fff07cf1c

def z972 : W := mkw 0x313dee003efd810a 0xc627bdc007dfb021 0x7ffffe30ffffa71f 0xefffffc61ffff4e3

def z973 : W := mkw 0x1f170bb137d7f7be 0x23e2e17626fafef7 0x67ff01f01fffffff 0xecffe03e03ffffff

def z974 : W := mkw 0xca1ff5fec1004434 0xf943febfd8200886 0xff9fffffe0000418 0x1ff3fffffc000083

def z975 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x8b98c1cf183e58e2 0xf1731839e307cb1c

def z976 : W := mkw 0xb03dee4a1efd8840 0xd607bdc943dfb108 0x7fffffcc1ffff867 0xeffffff983ffff0c

def z977 : W := mkw 0xc81ff5fec1005600 0xf903febfd8200ac0 0xffdffffff8007f04 0xfffbffffff000fe0

def z978 : W := mkw 0x10352e0016d58000 0x4206a5c002dab000 0x1fbf7e001fcf8003 0xe3f7efc003f9f000

def z979 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x637f01f01fc07f04 0xcc6fe03e03f80fe0

def z980 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xffbffe031fff8003 0xfff7ffc063fff000

def z981 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffffffffe7c07f05 0x1ffffffffcf80fe0

def z982 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe301fff8703 0xe3f7ffc603fff0e0

def z983 : W := mkw 0x0802112481004400 0x2100422490200880 0xffe7ff3fe7c06705 0xfffcffe7fcf80ce0

def z984 : W := mkw 0x101de60014c48000 0xc203bcc002989000 0x1fbffe001fcf8003 0xe3f7ffc003f9f000

def z985 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x6fff81f01ff07f07 0xedfff03e03fe0fe0

def z986 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xffd9c7fff8fe7fe7 0xfffb38ffff1fcffc

def z987 : W := mkw 0x0008e40000000000 0xc0011c8000000000 0xfe81fe33e0000000 0x1fd03fc67c000000

def z988 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe001809a 0x1ff3fffffc003013

def z989 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe03000e2 0x1ff3fffffc06001c

def z990 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x9f9ffe3fe0000000 0x13f3ffc7fc000000

def z991 : W := mkw 0xb03dee4a1efd8000 0xd607bdc943dfb000 0xffffffcf1ffff807 0xfffffff9e3ffff00

def z992 : W := mkw 0x0a02192483114434 0x2140432490622886 0xfda6b93fe731c4ff 0x7fb4d727fce6389f

def z993 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xfb9effcfe0000000 0x1f73dff9fc000000

def z994 : W := mkw 0x0a0219b483115634 0x2140433690622ac6 0xbda6b9ec8731dcff 0x77b4d73d90e63b9f

def z995 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x013eb8001f3f8002 0x4027d70003e7f000

def z996 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x77ff01f09fc1ff1d 0xeeffe03e13f83fe3

def z997 : W := mkw 0x4a0219b4c3114434 0x2940433698622886 0xbda6b93ce731c4ff 0x77b4d7279ce6389f

def z998 : W := mkw 0xc01df4dec0000000 0xd803be9bd8000000 0x4219fedf60000000 0x08433fdbec000000

def z999 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0xffffbffcffc07f05 0xfffff7ff9ff80fe0

def z1000 : W := mkw 0x15200a0136d7a18a 0x02a4014026daf431 0x0060000007cfa79f 0xa00c000000f9f4f3

def z1001 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x7ffffe001fffa007 0xefffffc003fff400

def z1002 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x56077e33e0000000 0x0ac0efc67c000000

def z1003 : W := mkw 0xc008f4dec0000000 0xd8011e9bd8000000 0xd800fedfe0000000 0x1b001fdbfc000000

def z1004 : W := mkw 0xc81ff5fec1004400 0xf903febfd8200880 0xffbfffffe7000401 0x1ff7fffffce00080

def z1005 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xefd9c1ff183e78e6 0xfdfb383fe307cf1c

def z1006 : W := mkw 0x0000080002110000 0x0000010000422000 0xbda6b92c8731c4ff 0x77b4d72590e6389f

def z1007 : W := mkw 0x0a00080003114434 0x0140010000622886 0xbda6b90c0731c4ff 0x77b4d72180e6389f

def z1008 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfc414633e0cfa79f 0x1f8828c67c19f4f3

def z1009 : W := mkw 0xa008c04a08280840 0x9401180941050108 0xab98c1cc183e58e6 0xf57318398307cb1c

def z1010 : W := mkw 0x30352e001efd8000 0x4606a5c003dfb000 0x14273e0007ff8003 0x0284e7c000fff000

def z1011 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x017e01c01fc07b00 0xc02fc03803f80f60

def z1012 : W := mkw 0x30352e001efd8000 0x4606a5c003dfb000 0x1ea77e001fff8003 0xe3d4efc003fff000

def z1013 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbfffc01fffd803 0xe3f7fff803fffb00

def z1014 : W := mkw 0x10150a0016d58000 0x0202a14002dab000 0x1fbffe001fff8003 0xe3f7ffc003fff000

def z1015 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x5ffffe101fffa303 0xebffffc203fff460

def z1016 : W := mkw 0xc01735fec0000000 0x7802e6bfd8000000 0x94073e3fe0000000 0x1280e7c7fc000000

def z1017 : W := mkw 0xae0ad96f8b3b6cf4 0xb5c15b2df1676d9e 0x567e78e39f0fbc19 0x8acfcf1c73e1f783

def z1018 : W := mkw 0x703dee905efd8000 0xce07bdd20bdfb000 0x1fbffe107fff8003 0xe3f7ffc20ffff000

def z1019 : W := mkw 0x15352e0136d7a18a 0x42a6a5c026daf431 0xf4673e33e7c1a79d 0x1e8ce7c67cf834f3

def z1020 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x007800c01fc07f05 0xe00f001803f80fe0

def z1021 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xf6414633e0cfa79d 0x9ec828c67c19f4f3

def z1022 : W := mkw 0xc81ff5fec1004400 0xf903febfd8200880 0xff9fffffe0004404 0x1ff3fffffc000880

def z1023 : W := mkw 0xc00235fec0000000 0x780046bfd8000000 0xf0003fffe0000000 0x1e0007fffc000000

def z1024 : W := mkw 0xca1decda43114434 0xd943bd9b48622886 0x423946d36731c4ff 0x684728da6ce6389f

def z1025 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffd9c7fff8ffffff 0xfffb38ffff1fffff

def z1026 : W := mkw 0x0a0219b483114434 0x2140433690622886 0xfda6b9fc8731c4ff 0x7fb4d73f90e6389f

def z1027 : W := mkw 0xc81ff5fec1004400 0xf903febfd8200880 0xffffffffff007c05 0xffffffffffe00f80

def z1028 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfec14633f8cfff9f 0xffd828c67f19fff3

def z1029 : W := mkw 0xb03dee4a1efd8000 0xd607bdc943dfb000 0x1fbfffcc1fff8003 0xe3f7fff983fff000

def z1030 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xefd9c1cf18fe78e7 0xfdfb3839e31fcf1c

def z1031 : W := mkw 0x0200180482110034 0x0040030090422006 0xbda6b90c8731c0ff 0x77b4d72190e6381f

def z1032 : W := mkw 0xe81ff5fedda85600 0xfd03febfdbb50ac0 0xfffffffffffe7f07 0xffffffffffffcfe0

def z1033 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x47ff01d01fc07b01 0xe8ffe03a03f80f60

def z1034 : W := mkw 0x0a0219b483115634 0x2140433690622ac6 0xbda6b93c8731c7ff 0x77b4d72790e638ff

def z1035 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0c00001 0xbff3fffffc180000

def z1036 : W := mkw 0xc01fe5fa40000000 0xf803fcbf48000000 0x7f9ffff360000000 0x0ff3fffe6c000000

def z1037 : W := mkw 0x0a0219b483115634 0x2140433690622ac6 0xffe7b9fc87f1ffff 0xfffcf73f90fe3fff

def z1038 : W := mkw 0x0015009014801200 0x0002a01202900240 0x427900d01fc03b01 0xe84f201a03f80760

def z1039 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xbc814633e0cf879f 0x379028c67c19f0f3

def z1040 : W := mkw 0xa508c04b282a29ca 0x94a1180965054539 0xefd9c1fff8fe7fff 0xfdfb383fff1fcfff

def z1041 : W := mkw 0x001de40014800000 0xc003bc8002900000 0xfffffe33ffc02705 0xffffffc67ff804e0

def z1042 : W := mkw 0x303dee000a7d8000 0xc607bdc0014fb000 0x1fbffe00073f8003 0x63f7ffc000e7f000

def z1043 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbda6ff2fe731c4ff 0x77b4dfe5fce6389f

def z1044 : W := mkw 0x3028ee000a7d8000 0xc6051dc0014fb000 0x1fbefe001f3f8003 0xe3f7dfc003e7f000

def z1045 : W := mkw 0x10352e0016d58000 0x4206a5c002dab000 0x1c277e0007cf8003 0x0384efc000f9f000

def z1046 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0x437fffdf7fc07b00 0xc86ffffbeff80f60

def z1047 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xe2414633e0cfa79f 0xbc4828c67c19f4f3

def z1048 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0x67ffffff7fc07f05 0xecffffffeff80fe0

def z1049 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe00e0002 0xbff3fffffc01c000

def z1050 : W := mkw 0x0015240000000000 0x4002a48000000000 0xfe877e33e0000000 0x1fd0efc67c000000

def z1051 : W := mkw 0x10352e0016d58000 0x4206a5c002dab000 0x16277e0007cf8001 0x82c4efc000f9f000

def z1052 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffdffffff8c07f04 0x9ffbffffff180fe0

def z1053 : W := mkw 0x35200a013effa18a 0x06a4014027dff431 0x006000001fffa303 0xe00c000003fff460

def z1054 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1bbefe001f3f8002 0xe377dfc003e7f000

def z1055 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x9fbffe03ffff8003 0xf3f7ffc07ffff000

def z1056 : W := mkw 0xe01ff5fec8280840 0xfc03febfd9050108 0xff9ffffff83058e6 0x7ff3ffffff060b1c

def z1057 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x9806fe0fe0000000 0x1300dfc1fc000000

def z1058 : W := mkw 0xc00af5fec0000000 0xf8015ebfd8000000 0x9800fe3fe0000000 0x13001fc7fc000000

def z1059 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x4358c1cf183e78e6 0xe86b1839e307cf1c

def z1060 : W := mkw 0xc21ff5fec0000034 0xf843febfd8000006 0xff9fffffe00000f8 0x1ff3fffffc00001f

def z1061 : W := mkw 0x0a02192483114434 0x2140432490622886 0xb926b92c8731c4fe 0x5724d72590e6389f

def z1062 : W := mkw 0x001fe5b000000000 0xe003fcb600000000 0xff9ffff3e0000000 0x1ff3fffe7c000000

def z1063 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xffd8c1cf183ff8e7 0xfffb1839e307ff1c

def z1064 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1ebf7e001fcf8003 0xa3d7efc003f9f000

def z1065 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x66f900f01fc07f05 0xecdf201e03f80fe0

def z1066 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffbfffffffc00701 0xfff7fffffff800e0

def z1067 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xde414633e0cfa79b 0x9bc828c67c19f4f3

def z1068 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x617e01f01fc07f05 0xec2fc03e03f80fe0

def z1069 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbfa6f92c873fc4ff 0xf7f4df2590e7f89f

def z1070 : W := mkw 0xa508c04b282a29ca 0x94a1180965054539 0xffd8c1fff83fffff 0xfffb183fff07ffff

def z1071 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbda6b92c8731c0fa 0x57b4d72590e6381f

def z1072 : W := mkw 0x2008c8000a390000 0x8401190001472000 0x1da6f800073f8003 0x63b4df0000e7f000

def z1073 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x667f01f01fc07f05 0x8ccfe03e03f80fe0

def z1074 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xf51fbfffe0000000 0x1ea3f7fffc000000

def z1075 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x013eb8001f3e0002 0xe027d70003e7c000

def z1076 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xea58c1cf183e78e6 0x9d4b1839e307cf1c

def z1077 : W := mkw 0xc00af5fec0000000 0xf8015ebfd8000000 0xfb98ffffe0000000 0x1f731ffffc000000

def z1078 : W := mkw 0x30200a001efd8000 0x0604014003dfb000 0x1fa7fe001fff8003 0xe3f4ffc003fff000

def z1079 : W := mkw 0xa508c04b282a29ca 0x94a1180965054539 0xebd8c1cff83e78fe 0xfd7b1839ff07cf1f

def z1080 : W := mkw 0x2a0ad12489284434 0xa5415a2491250886 0xab98c12c983e44fe 0xf57318259307c89f

def z1081 : W := mkw 0x8e02116f81026cf4 0x31c0422df0204d9e 0xa000012f800044fc 0x14000025f000089f

def z1082 : W := mkw 0x3f000a012b7fedfe 0x07e00140256ffdbf 0x006000001fffffff 0xe00c000003ffffff

def z1083 : W := mkw 0x0a02192483114434 0x2140432490622886 0x1526b92c8731c4ff 0x62a4d72590e6389f

def z1084 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0x9c27fe3fe7c00701 0x1384ffc7fcf800e0

def z1085 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0xff9ffef3e0000000 0x1ff3ffde7c000000

def z1086 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd8c1ff183e7fe6 0xfd7b183fe307cffc

def z1087 : W := mkw 0xc008e44a40000000 0xd8011c8948000000 0x1800fe0360000000 0x03001fc06c000000

def z1088 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1b3ffe001fff8002 0xc367ffc003fff000

def z1089 : W := mkw 0x10352e0016d58000 0x4206a5c002dab000 0x1fa7fe0007ff8003 0xe3f4ffc000fff000

def z1090 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xf4073e33e0000000 0x1e80e7c67c000000

def z1091 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xda18fecfe0000000 0x1b431fd9fc000000

def z1092 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x093ef8001f3e0002 0x4127df0003e7c000

def z1093 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xb980ff0fe03040e6 0x77301fe1fc06081c

def z1094 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0x67ff39f01fc07f05 0xecffe73e03f80fe0

def z1095 : W := mkw 0x1a373fb497d5d634 0x6346e7f692fabac6 0x14273e3087c18719 0x0284e7c610f830e3

def z1096 : W := mkw 0x0a02192483114434 0x2140432490622886 0xffbeb9ec8731c4ff 0x7ff7d73d90e6389f

def z1097 : W := mkw 0x0a02192483114434 0x2140432490622886 0xffe7ff3fe7f1e7ff 0xfffcffe7fcfe3cff

def z1098 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x9e81fe0fe0000000 0x13d03fc1fc000000

def z1099 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdffffff83078e6 0xfffbffffff060f1c

def z1100 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbfbeb92c9f31c4ff 0xf7f7d72593e6389f

def z1101 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x033ffe001fff8003 0xe067ffc003fff000

def z1102 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1826fe00073f8002 0x0304dfc000e7f000

def z1103 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffbfffffe7c04705 0x7ff7fffffcf808e0

def z1104 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x9e814633e0cf879b 0xb3d028c67c19f0f3

def z1105 : W := mkw 0x0a00080003114434 0x0140010000622886 0xfea14633e731c4ff 0x7fd428c67ce6389f

def z1106 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe00040e4 0x1ff3fffffc00081c

def z1107 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff47f3ffc1ff9f 0xffffe8fe7ff83ff3

def z1108 : W := mkw 0x0015009014801200 0x0002a01202900240 0x437f00d01fc03b00 0xc86fe01a03f80760

def z1109 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xe958c1cf183e78e6 0x5d2b1839e307cf1c

def z1110 : W := mkw 0x35350a013effa18a 0x06a6a14027dff431 0x67ff00301fffa79f 0xecffe00603fff4f3

def z1111 : W := mkw 0xc01735fec0000000 0x7802e6bfd8000000 0xfe877fffe0000000 0x1fd0effffc000000

def z1112 : W := mkw 0x303dee001efd9200 0xc607bdc003dfb240 0x1ffffe001fffbb03 0xe3ffffc003fff760

def z1113 : W := mkw 0x1f000a012357e5be 0x03e00140246afcb7 0x0060000007cfa79f 0xa00c000000f9f4f3

def z1114 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd8c1cf18fe7fe7 0xfd7b1839e31fcffc

def z1115 : W := mkw 0xc01df44ec0000000 0xd803be89d8000000 0x9a19fe0fe0000000 0x13433fc1fc000000

def z1116 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xffd8c1ef983e78e6 0xfffb183df307cf1c

def z1117 : W := mkw 0x303dee901efd9200 0xc607bdd203dfb240 0x7ffffef01fffbf07 0xefffffde03fff7e0

def z1118 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0x431ffed360000000 0x0863ffda6c000000

def z1119 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffbfffffffc05801 0xfff7fffffff80b00

def z1120 : W := mkw 0xc00af56ec0000000 0xf8015eadd8000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z1121 : W := mkw 0x313dee003efd810a 0xc627bdc007dfb021 0xbfbffe30ffff879f 0xf7f7ffc61ffff0f3

def z1122 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xbfbffe209fff8003 0xf7f7ffc413fff000

def z1123 : W := mkw 0x0802012001004400 0x2100402400200880 0x67ff01f01fc07f05 0xecffe03e03f80fe0

def z1124 : W := mkw 0xb03dee4a1efd8000 0xd607bdc943dfb000 0xffbfffffffff8003 0xfff7fffffffff000

def z1125 : W := mkw 0x0a1711b495805634 0x2142e23692b00ac6 0xefff81fc9ff07fff 0xfdfff03f93fe0fff

def z1126 : W := mkw 0x35200a012a7fa18a 0x06a40140254ff431 0x00000000003f809a 0x000000000007f013

def z1127 : W := mkw 0x0f021125a10265be 0x21e04224b4204cb7 0xe0400033e000279c 0x1c0800067c0004f3

def z1128 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x77ff07f0ffc07f05 0xeeffe0fe1ff80fe0

def z1129 : W := mkw 0xc81ff5fed5805600 0xf903febfdab00ac0 0xffffffffe7c02705 0xbffffffffcf804e0

def z1130 : W := mkw 0xc01df44ec0000000 0xd803be89d8000000 0xff9ffe3fe0000000 0x1ff3ffc7fc000000

def z1131 : W := mkw 0x3028ca001efd8000 0x8605194003dfb000 0x1fbef8001fff8003 0xe3f7df0003fff000

def z1132 : W := mkw 0xf03deeda5efd8000 0xde07bddb4bdfb000 0xffbfffdf7fff8003 0xfff7fffbeffff000

def z1133 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x013efe001f3e0000 0x4027dfc003e7c000

def z1134 : W := mkw 0xc01de4da54801200 0xd803bc9b4a900240 0x5ffffed37fc03b01 0xebffffda6ff80760

def z1135 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xe7ff01f3ffc07f05 0xfcffe03e7ff80fe0

def z1136 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xbfbffe001fff8087 0xf7f7ffc003fff010

def z1137 : W := mkw 0x15000a012257a18a 0x02a00140244af431 0x0060000007ffa79f 0xe00c000000fff4f3

def z1138 : W := mkw 0x24000001082a28c0 0x0480000021054518 0xebd881cc183e78e6 0xfd7b10398307cf1c

def z1139 : W := mkw 0xe01ff5fec8280000 0xfc03febfd9050000 0xff9ffffff83e40e6 0xfff3ffffff07c81c

def z1140 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xe15881cf183e78e6 0xfc2b1039e307cf1c

def z1141 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z1142 : W := mkw 0xe01ff5fec8280000 0xfc03febfd9050000 0xff9ffffff8300000 0x5ff3ffffff060000

def z1143 : W := mkw 0x313dee003efd810a 0xc627bdc007dfb021 0x1fbffe00ffff801b 0xe3f7ffc01ffff003

def z1144 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x25fe01e01fc07f05 0xe4bfc03c03f80fe0

def z1145 : W := mkw 0x110002002044810a 0x0220004004089021 0xfe814633e0cf871b 0xbfd028c67c19f0e3

def z1146 : W := mkw 0xca1ff5fec1005634 0xf943febfd8200ac6 0xffdfffffe0007ffc 0x1ffbfffffc000fff

def z1147 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe000049c 0x1ff3fffffc000093

def z1148 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xffd9c7fff83ffcff 0xfffb38ffff07ff9f

def z1149 : W := mkw 0xc000344ec0000000 0x58000689d8000000 0x90003e0fe0000000 0x120007c1fc000000

def z1150 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0xe7ff01fc9fc07f05 0xfcffe03f93f80fe0

def z1151 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x9f9fffcfe0000000 0x13f3fff9fc000000

def z1152 : W := mkw 0x17000a012257a1be 0x02e00140244af437 0x00000000003f80fa 0x000000000007f01f

def z1153 : W := mkw 0x3028ee000a7d8000 0xc6051dc0014fb000 0x1c26fe00073f8003 0x0384dfc000e7f000

def z1154 : W := mkw 0xc81ff5fec1004400 0xf903febfd8200880 0xffffffffe7c06705 0xfffffffffcf80ce0

def z1155 : W := mkw 0xb03dee4a1efd8840 0xd607bdc943dfb108 0xffbfffcf1fffd863 0xfff7fff9e3fffb0c

def z1156 : W := mkw 0x10000a0002558000 0x02000140004ab000 0x1ea77e0007cf8003 0xa3d4efc000f9f000

def z1157 : W := mkw 0xc01de44a40000000 0xd803bc8948000000 0x1f9ffe0360000000 0x03f3ffc06c000000

def z1158 : W := mkw 0x001ff52480000000 0xe003fea490000000 0xff9fff3fe0000000 0x1ff3ffe7fc000000

def z1159 : W := mkw 0x30352e001efd8000 0x4606a5c003dfb000 0x1da7be001fff8003 0xe3b4f7c003fff000

def z1160 : W := mkw 0xb03dee4a1efd8000 0xd607bdc943dfb000 0xffbfffcf1fffc0e7 0xfff7fff9e3fff81c

def z1161 : W := mkw 0x1f020b212357e5be 0x23e04164246afcb7 0x67e7013007ffe7ff 0xecfce02600fffcff

def z1162 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0xfee77e33e7c02705 0xbfdcefc67cf804e0

def z1163 : W := mkw 0xe008f44ec8280000 0xdc011e89d9050000 0x9b98fe0ff83e0002 0xf3731fc1ff07c000

def z1164 : W := mkw 0x0802012015805600 0x2100402402b00ac0 0x67fe01e01fc07f05 0xecffc03c03f80fe0

def z1165 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdfffffe0c1a79f 0xbffbfffffc1834f3

def z1166 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x9c077e33e0000000 0x1380efc67c000000

def z1167 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffc7fe33e0cfa79f 0xbff8ffc67c19f4f3

def z1168 : W := mkw 0x30352e001efd8000 0x4606a5c003dfb000 0x002638001fff8003 0xe004c70003fff000

def z1169 : W := mkw 0xca1ff5fed5805634 0xf943febfdab00ac6 0xffffffffffc07ffd 0xfffffffffff80fff

def z1170 : W := mkw 0xa508c04b282a29ca 0x94a1180965054539 0xebd8c1cf183e7ffe 0xfd7b1839e307cfff

def z1171 : W := mkw 0x0a02192483114434 0x2140432490622886 0x9d26b92c8731c4fb 0x53a4d72590e6389f

def z1172 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe001f3f8002 0x43f7ffc003e7f000

def z1173 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x477f01f01fc07f01 0xc8efe03e03f80fe0

def z1174 : W := mkw 0x3008ca000a7d8000 0x86011940014fb000 0x1fbffe001fff8003 0xe3f7ffc003fff000

def z1175 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff01f09fc07f05 0xffffe03e13f80fe0

def z1176 : W := mkw 0x0015009014801200 0x0002a01202900240 0x467f00d01fc03b01 0x88cfe01a03f80760

def z1177 : W := mkw 0x303dee901efd8000 0xc607bdd203dfb000 0x5fbffed01fff8003 0xebf7ffda03fff000

def z1178 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff81fc9ff1ffff 0xfffff03f93fe3fff

def z1179 : W := mkw 0x0a02192483114434 0x2140432490622886 0xb9a6b90c8731c0fe 0x7734d72190e6381f

def z1180 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff01f01fc1ff9f 0xecffe03e03f83ff3

def z1181 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xf61f7fffe0000000 0x1ec3effffc000000

def z1182 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x9800fe0fe001809a 0x13001fc1fc003013

def z1183 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x9800fe0fe03000e2 0x13001fc1fc06001c

def z1184 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbca6b82c873184ff 0x3794d70590e6309f

def z1185 : W := mkw 0xf03deeda5efd8000 0xde07bddb4bdfb000 0x1fbffec01fff8003 0xe3f7ffd803fff000

def z1186 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x779f7ff3e0000000 0x0ef3effe7c000000

def z1187 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xbc80fe2fe001849f 0x37901fc5fc003093

def z1188 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x437f01d01fc07f05 0xe86fe03a03f80fe0

def z1189 : W := mkw 0x8f02116fa1026dfe 0x31e0422df4204dbf 0xe04001ffe0007ffc 0x1c08003ffc000fff

def z1190 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x5fbffe137fff8003 0xebf7ffc26ffff000

def z1191 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x67f901f01fc07f05 0xecff203e03f80fe0

def z1192 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xf800fe3fe0000000 0x1f001fc7fc000000

def z1193 : W := mkw 0xc81ff5fed5804400 0xf903febfdab00880 0xffbfffffffc04405 0xfff7fffffff80880

def z1194 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff01f01fc03f01 0x8cffe03e03f807e0

def z1195 : W := mkw 0xc81ff5fec1005600 0xf903febfd8200ac0 0xffdfffffe0c07f05 0xbffbfffffc180fe0

def z1196 : W := mkw 0xb528ee4b2a7fa9ca 0xd6a51dc9654ff539 0x9800fe0fe03f80fa 0x13001fc1fc07f01f

def z1197 : W := mkw 0x0202192482110034 0x2040432490422006 0xbda6b92c873180fb 0x77b4d72590e6301f

def z1198 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x9b98fe0fe0000000 0x13731fc1fc000000

def z1199 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x0118c1cf183e5860 0x40231839e307cb0c

def z1200 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0000086 0x3ff3fffffc000010

def z1201 : W := mkw 0x8e02116f81026cf4 0x31c0422df0204d9e 0xe04001cf000078e4 0x1c080039e0000f1c

def z1202 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0xffffb9fc9ff07fe7 0xfffff73f93fe0ffc

def z1203 : W := mkw 0x35200a013effa9ca 0x06a4014027dff539 0x006000001fffffff 0xe00c000003ffffff

def z1204 : W := mkw 0xb03dee4a1efd8840 0xd607bdc943dfb108 0xbfbfffcc1fffd8e7 0xf7f7fff983fffb1c

def z1205 : W := mkw 0xc01ff5fec0001200 0xf803febfd8000240 0xffdfffffe0003b00 0x1ffbfffffc000760

def z1206 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfe814633e0cf879b 0x1fd028c67c19f0f3

def z1207 : W := mkw 0x8e0211ff81027ef4 0x31c0423ff0204fde 0xe04001ff80007ffc 0x1c08003ff0000fff

def z1208 : W := mkw 0xc00af5fec0000000 0xf8015ebfd8000000 0x9800ffcfe0000000 0x13001ff9fc000000

def z1209 : W := mkw 0xc81ff5fec1004400 0xf903febfd8200880 0xffbfffffe701c49f 0x7ff7fffffce03893

def z1210 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe001ffe0000 0xc3f7ffc003ffc000

def z1211 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1dbeb8001fff8003 0xe3b7d70003fff000

def z1212 : W := mkw 0x10352e0016d58000 0x4206a5c002dab000 0x14273e0007cf8003 0xa284e7c000f9f000

def z1213 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xfc07ffffe0000000 0x1f80fffffc000000

def z1214 : W := mkw 0x0a02192483114434 0x2140432490622886 0x1da6b90c0731c4ff 0x63b4d72180e6389f

def z1215 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1ffffe001ffff807 0xe3ffffc003ffff00

def z1216 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x023f7e001fce0000 0x8047efc003f9c000

def z1217 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x07bffe001ffe0001 0xe0f7ffc003ffc000

def z1218 : W := mkw 0xc01df4dec0000000 0xd803be9bd8000000 0x9818fecfe0000000 0x13031fd9fc000000

def z1219 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x8958c1cf183e78e6 0xf12b1839e307cf1c

def z1220 : W := mkw 0xb708da4faa7fa9fe 0x96e11b49f54ff53f 0x9800fe0fe03f80fa 0x13001fc1fc07f01f

def z1221 : W := mkw 0x0015009014801200 0x0002a01202900240 0x67ff00f01fc03f05 0xecffe01e03f807e0

def z1222 : W := mkw 0x30200a001efd8000 0x0604014003dfb000 0x0126b8001fff8003 0xe024d70003fff000

def z1223 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0304060 0x5ff3fffffc06080c

def z1224 : W := mkw 0x401ff5b4c0000000 0xe803feb698000000 0xff9ffe33e0000000 0x1ff3ffc67c000000

def z1225 : W := mkw 0x0002112480000000 0x2000422490000000 0xfe877e33e0000000 0x1fd0efc67c000000

def z1226 : W := mkw 0xc00af5fec0000000 0xf8015ebfd8000000 0xfd86ffffe0000000 0x1fb0dffffc000000

def z1227 : W := mkw 0xe01ff5fec8280840 0xfc03febfd9050108 0xff9fffffe0300060 0x1ff3fffffc06000c

def z1228 : W := mkw 0x35200a013effa18a 0x06a4014027dff431 0x002000001fff809b 0xe004000003fff013

def z1229 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x3fbfff001fffc007 0xe7f7ffe003fff800

def z1230 : W := mkw 0x0000080002110000 0x0000010000422000 0x1fa6f800073f8003 0xe3f4df0000e7f000

def z1231 : W := mkw 0x40003404c0000000 0x4800068098000000 0xfe817e33e0000000 0x1fd02fc67c000000

def z1232 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe209fff841b 0xe3f7ffc413fff083

def z1233 : W := mkw 0x10000a0002558000 0x02000140004ab000 0x1da6fe00073f8003 0x63b4dfc000e7f000

def z1234 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xfffffe309fffa79f 0xffffffc613fff4f3

def z1235 : W := mkw 0xca1ff5fec1004434 0xf943febfd8200886 0xff9fffffe001c4ff 0x3ff3fffffc00389f

def z1236 : W := mkw 0xc01ff5fed4801200 0xf803febfda900240 0xff9ffffff8001800 0x1ff3ffffff000300

def z1237 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x7fbffe301fff8003 0xeff7ffc603fff000

def z1238 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x14077e33e0000000 0x0280efc67c000000

def z1239 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xe358c1cf183e78e4 0xdc6b1839e307cf1c

def z1240 : W := mkw 0x0008e40000000000 0xc0011c8000000000 0x9800fe03e0000000 0x13001fc07c000000

def z1241 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfec14633e0cfa719 0x9fd828c67c19f4e3

def z1242 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x0fbff8001ffe0003 0xe1f7ff0003ffc000

def z1243 : W := mkw 0x0a02192483114434 0x2140432490622886 0xffffb9fc9ff1ffff 0xfffff73f93fe3fff

def z1244 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xffd9c1ff98ffffff 0xfffb383ff31fffff

def z1245 : W := mkw 0xc208f44ec0000034 0xd8411e89d8000006 0x9800fe0fe00000f8 0x13001fc1fc00001f

def z1246 : W := mkw 0x0a02192483114434 0x2140432490622886 0xa126b92c8731c4ff 0x7424d72590e6389f

def z1247 : W := mkw 0x801de44a00000000 0xd003bc8940000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z1248 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xf91effffe0000000 0x1f23dffffc000000

def z1249 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0018419 0x1ff3fffffc003083

def z1250 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1ea7fe0007ff8003 0xa3d4ffc000fff000

def z1251 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xbd87ff3fe0000000 0x17b0ffe7fc000000

def z1252 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xfbd8ffcff8007804 0xff7b1ff9ff000f00

def z1253 : W := mkw 0xf03dee4a5efd8000 0xde07bdc94bdfb000 0x1fbffe037fff8003 0xe3f7ffc06ffff000

def z1254 : W := mkw 0xa508c04b282a29ca 0x94a1180965054539 0xebd8c1df783e7be6 0xfd7b183bef07cf7c

def z1255 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xebd9c7df783e78e6 0xfd7b38fbef07cf1c

def z1256 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x427f00d01fc03b00 0x884fe01a03f80760

def z1257 : W := mkw 0xc80af5fec1005600 0xf9015ebfd8200ac0 0xf840ffffe0007f04 0x1f081ffffc000fe0

def z1258 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x63d8c1cf183e7864 0xec7b1839e307cf0c

def z1259 : W := mkw 0xf03deeda5efd8000 0xde07bddb4bdfb000 0xffbffef3ffff8003 0xfff7ffde7ffff000

def z1260 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x657f01f01fc07f05 0x4cafe03e03f80fe0

def z1261 : W := mkw 0x303dee901efd9200 0xc607bdd203dfb240 0x1fbffec01fff9803 0xe3f7ffd803fff300

def z1262 : W := mkw 0xc00211fec0000000 0x3800423fd8000000 0xff87ffffe0000000 0x1ff0fffffc000000

def z1263 : W := mkw 0x1a0213248144c434 0x2340426490289886 0xbe81472c80cfc4ff 0xb7d028e59019f89f

def z1264 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x427800c01fc07f05 0xe84f001803f80fe0

def z1265 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1c27fe001fff8003 0xe384ffc003fff000

def z1266 : W := mkw 0x0015009014801200 0x0002a01202900240 0x67ff01d01fc07b05 0xecffe03a03f80f60

def z1267 : W := mkw 0x3028ee000a7d8000 0xc6051dc0014fb000 0x1926fe00073f8002 0x4324dfc000e7f000

def z1268 : W := mkw 0xa008c04a08280840 0x9401180941050108 0x011881cc183e5862 0xe02310398307cb0c

def z1269 : W := mkw 0xc01df44ec0000000 0xd803be89d8000000 0xff9fffcfe0000000 0x1ff3fff9fc000000

def z1270 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xff99ffffe0000000 0x1ff33ffffc000000

def z1271 : W := mkw 0xca1ff5fec1004434 0xf943febfd8200886 0xffbfffffe70044fd 0x7ff7fffffce0089f

def z1272 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xbfbfff2c9fffc4ff 0xf7f7ffe593fff89f

def z1273 : W := mkw 0x0a02192483114434 0x2140432490622886 0x9926b90c8731c4ff 0x7324d72190e6389f

def z1274 : W := mkw 0x481725b055805600 0x6902e4b60ab00ac0 0x67ff07f07fc07f05 0xecffe0fe0ff80fe0

def z1275 : W := mkw 0xc01ff5fed4800000 0xf803febfda900000 0xffbfffffff000000 0x5ff7ffffffe00000

def z1276 : W := mkw 0xe01ff5fec8280000 0xfc03febfd9050000 0xff9fffffe03e0002 0x1ff3fffffc07c000

def z1277 : W := mkw 0x0000000000000000 0x0000000000000000 0xff87fe33e0000000 0x1ff0ffc67c000000

def z1278 : W := mkw 0x0e021125810264b4 0x21c04224b0204c96 0xe040012f800064fc 0x1c080025f0000c9f

def z1279 : W := mkw 0xc81735fed5805600 0x7902e6bfdab00ac0 0xf7ff3fffffc07f05 0xfeffe7fffff80fe0

def z1280 : W := mkw 0x0000100480000000 0x0000020090000000 0xfe81fe3fe0000000 0x1fd03fc7fc000000

def z1281 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbdbeb9ec9f31dcff 0x77b7d73d93e63b9f

def z1282 : W := mkw 0xc81fe5fa55805600 0xf903fcbf4ab00ac0 0x7ffffff37fc07f05 0xeffffffe6ff80fe0

def z1283 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xfbd8c1cf983ff8fe 0xff7b1839f307ff1f

def z1284 : W := mkw 0x081725b015805600 0x6102e4b602b00ac0 0x77ff3ff01fc07f05 0xeeffe7fe03f80fe0

def z1285 : W := mkw 0xc81ff5fec1004400 0xf903febfd8200880 0xffbfffffe73044e7 0x7ff7fffffce6089c

def z1286 : W := mkw 0x0a02192483114434 0x2140432490622886 0x9da6b90c8731c0fb 0x73b4d72190e6381f

def z1287 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbde6b92c87f1e7ff 0xf7bcd72590fe3cff

def z1288 : W := mkw 0x0400000100022080 0x0080000020004410 0xebd8c1cf183e78e6 0xfd7b1839e307cf1c

def z1289 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x427900d01fc03f01 0x884f201a03f807e0

def z1290 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1da7fe0007ff8003 0x63b4ffc000fff000

def z1291 : W := mkw 0x0a02192483114434 0x2140432490622886 0xffe6b92c8731e4ff 0xfffcd72590e63c9f

def z1292 : W := mkw 0x0a1711b495805634 0x2142e23692b00ac6 0x67ff01f09fc07f1d 0xecffe03e13f80fe3

def z1293 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xffd947f3e0cfa79f 0xbffb28fe7c19f4f3

def z1294 : W := mkw 0x103dee0016d58000 0xc207bdc002dab000 0x1fbffe0007cf8003 0xa3f7ffc000f9f000

def z1295 : W := mkw 0x17000a012257a1be 0x02e00140244af437 0x0040000000ffa7ff 0xa0080000001ff4ff

def z1296 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0x679fffff60000000 0x0cf3ffffec000000

def z1297 : W := mkw 0x0815000015805600 0x0102a00002b00ac0 0x67ff01c01fc07f05 0xecffe03803f80fe0

def z1298 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9fffffe0018003 0x3ff3fffffc003000

def z1299 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdffffff8003800 0x9ffbffffff000700

def z1300 : W := mkw 0x0a02192483114434 0x2140432490622886 0xbfa7b92c87f1c4ff 0xf7f4f72590fe389f

def z1301 : W := mkw 0xc01de4da40000000 0xd803bc9b48000000 0x5a19fed360000000 0x0b433fda6c000000

def z1302 : W := mkw 0xa008c04a08280840 0x9401180941050108 0x0918c1cc183e5862 0x412318398307cb0c

def z1303 : W := mkw 0xe81ff5fedda85e40 0xfd03febfdbb50bc8 0xffbfffffff305860 0x5ff7ffffffe60b0c

def z1304 : W := mkw 0xa43dec4b1ebb28c0 0xd487bd8963d76518 0xe17eb9cf1f3078e4 0x5c2fd739e3e60f1c

def z1305 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe30ffff8003 0xe3f7ffc61ffff000

def z1306 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0x67ffb9fc1fc07f05 0xecfff73f83f80fe0

def z1307 : W := mkw 0x080201b015805600 0x2100403602b00ac0 0x63f801f01fc07f05 0xec7f003e03f80fe0

def z1308 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x173ffe001fff8001 0xc2e7ffc003fff000

def z1309 : W := mkw 0x150002012046a18a 0x02a000402408d431 0x56414633e0cfa79f 0xaac828c67c19f4f3

def z1310 : W := mkw 0x30352e001efd8000 0x4606a5c003dfb000 0x14273e001fcf8001 0x8284e7c003f9f000

def z1311 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x47ff00d01fc07f05 0xe8ffe01a03f80fe0

def z1312 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe001fffc0e7 0xe3f7ffc003fff81c

def z1313 : W := mkw 0xe01ff5fec8280840 0xfc03febfd9050108 0xffdffffff8307864 0xfffbffffff060f0c

def z1314 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1ffffe001fffa707 0xe3ffffc003fff4e0

def z1315 : W := mkw 0x203dec001eb90000 0xc407bd8003d72000 0x1fbef8001f3f8003 0xe3f7df0003e7f000

def z1316 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xefd8c1ef183e7ce7 0xfdfb183de307cf9c

def z1317 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0xffffffcc1ffff8e7 0xfffffff983ffff1c

def z1318 : W := mkw 0x3d200a013ffff78a 0x07a4014027fffef1 0x006000001fffff9f 0xe00c000003fffff3

def z1319 : W := mkw 0xc01df44ed4800000 0xd803be89da900000 0x9fbffe0fffc00001 0xf3f7ffc1fff80000

def z1320 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xa998c1cf183e58e6 0x75331839e307cb1c

def z1321 : W := mkw 0x303dee001efd8000 0xc607bdc003dfb000 0x1fbffe001fff849f 0xe3f7ffc003fff093

def z1322 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffdfffffe0007804 0x1ffbfffffc000f00

def z1323 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0xcb58c1cf183e78e2 0xd96b1839e307cf1c

def z1324 : W := mkw 0xb03dee4a1efd8840 0xd607bdc943dfb108 0x1fbffe0c1fff8063 0xe3f7ffc183fff00c

def z1325 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x9f9ffe03e0000000 0x13f3ffc07c000000

def z1326 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67ff01f01fc07f05 0xecffe03e03f80fe0

def z1327 : W := mkw 0x2008c8000a390000 0x8401190001472000 0x0bbef8001f3e0002 0xe177df0003e7c000

def z1328 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x5f9ffe1360000000 0x0bf3ffc26c000000

def z1329 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x07ff01c01fc07f05 0xe0ffe03803f80fe0

def z1330 : W := mkw 0xb03dee4a1efd8000 0xd607bdc943dfb000 0x5fbffec31fff8003 0xebf7ffd863fff000

def z1331 : W := mkw 0xc01df44ec0000000 0xd803be89d8000000 0x9c07fe0fe0000000 0x1380ffc1fc000000

def z1332 : W := mkw 0x1f000a0137d7f7be 0x03e0014026fafef7 0x006000001fffffff 0xe00c000003ffffff

def z1333 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0x9c01fe3fe0000000 0x13803fc7fc000000

def z1334 : W := mkw 0x3d370bb13ffff78a 0x27a6e17627fffef1 0x67ff01f01fffff9f 0xecffe03e03fffff3

def z1335 : W := mkw 0xc008f44ec0000000 0xd8011e89d8000000 0xf800ffcfe0000000 0x1f001ff9fc000000

def z1336 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xffbfffffe7000001 0x7ff7fffffce00000

def z1337 : W := mkw 0xca1ff5fec1004434 0xf943febfd8200886 0xff9fffffe03044fe 0x7ff3fffffc06089f

def z1338 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x015881cc183e7860 0xc02b10398307cf0c

def z1339 : W := mkw 0xc01df4ded4801200 0xd803be9bda900240 0xda59fedff8c03b00 0x9b4b3fdbff180760

def z1340 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xfe9f7ef3e0000000 0x1fd3efde7c000000

def z1341 : W := mkw 0xa408c04b082a28c0 0x9481180961054518 0x4bd8c1cf183e7862 0xe97b1839e307cf0c

def z1342 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x7fffb9f01fc07f05 0xeffff73e03f80fe0

def z1343 : W := mkw 0xb53de64b3ceea9ca 0xd6a7bcc9679dd539 0x425946d378ce3b00 0x884b28da6f19c760

def z1344 : W := mkw 0x150002012046a18a 0x02a000402408d431 0xfa414633e0cfa79e 0x9f4828c67c19f4f3

def z1345 : W := mkw 0xc01ff5fec0000000 0xf803febfd8000000 0xff9ffffff8005800 0x5ff3ffffff000b00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z2,z3,z5,z6]),(0,[z8,z0,z9,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z5,z11]),(0,[z0,z1,z2,z3,z12,z5,z6]),(1,[z0,z1,z2,z13,z5,z14]),(0,[z0,z1,z2,z15,z3,z5,z6])],[(0,[z16,z0,z17,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z6]),(1,[z19,z1,z20,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z22]),(0,[z23,z1,z2,z3,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z25]),(0,[z0,z1,z2,z3,z26,z5,z27])],[(0,[z0,z28,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z29,z6]),(1,[z21,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z31,z30]),(0,[z0,z1,z2,z13,z3,z5,z30]),(0,[z0,z1,z32,z2,z3,z5,z6]),(0,[z0,z1,z2,z33,z5,z34,z6]),(0,[z0,z10,z1,z35,z2,z3,z5]),(0,[z0,z1,z2,z3,z36,z5,z6]),(0,[z0,z1,z2,z3,z37,z5,z6])],[(0,[z0,z1,z2,z38,z3,z5,z6]),(0,[z0,z1,z2,z39,z3,z5,z6]),(0,[z0,z1,z2,z3,z40,z41,z5]),(0,[z42,z0,z1,z2,z3,z5,z43]),(0,[z0,z1,z44,z2,z5,z6,z27]),(0,[z0,z1,z2,z3,z5,z6,z45])],[(0,[z1,z17,z2,z46,z3,z5,z6]),(0,[z47,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z46,z3,z48,z5,z6]),(0,[z0,z1,z2,z49,z3,z5,z6]),(1,[z50,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z51]),(0,[z0,z1,z52,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z53,z48,z5,z6]),(0,[z0,z1,z2,z54,z3,z5,z6]),(0,[z0,z1,z2,z3,z55,z5,z6]),(0,[z56,z0,z1,z57,z3,z5,z6])],[(0,[z0,z9,z2,z3,z5,z6,z58]),(0,[z0,z1,z2,z59,z3,z5,z6])],[(1,[z60,z0,z1,z3,z31,z6]),(0,[z0,z1,z2,z61,z3,z5,z6]),(0,[z0,z1,z2,z62,z3,z5,z63])]],
   [[(1,[z0,z1,z2,z3,z5,z64]),(0,[z16,z1,z2,z46,z3,z5,z6]),(0,[z0,z1,z2,z3,z65,z66,z6]),(0,[z0,z1,z44,z2,z3,z5,z67]),(0,[z0,z1,z2,z68,z3,z5,z67]),(0,[z0,z2,z3,z5,z11,z6,z58]),(0,[z0,z1,z2,z62,z41,z5,z6]),(0,[z69,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z70]),(0,[z0,z1,z71,z2,z3,z5,z6]),(0,[z0,z1,z2,z72,z3,z5,z6]),(0,[z0,z1,z2,z68,z3,z26,z6])],[(0,[z0,z1,z2,z3,z5,z6,z73]),(0,[z74,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z54,z3,z5,z31,z6]),(0,[z0,z1,z2,z3,z5,z6,z75]),(1,[z0,z1,z2,z3,z76,z77])],[(1,[z19,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z30,z43]),(0,[z0,z1,z2,z78,z5,z79,z6]),(0,[z0,z1,z2,z3,z5,z80,z6]),(0,[z0,z1,z2,z3,z81,z5,z6]),(1,[z0,z1,z2,z3,z82,z6])],[(0,[z1,z17,z2,z3,z5,z6,z30]),(0,[z83,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z84,z6]),(0,[z0,z1,z85,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z86,z5,z30]),(0,[z8,z0,z2,z54,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z66,z30]),(1,[z1,z2,z3,z24,z5,z30]),(0,[z0,z1,z2,z3,z87,z5,z6]),(1,[z0,z88,z2,z3,z5,z6]),(0,[z0,z1,z44,z2,z13,z5,z6]),(0,[z89,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z26,z90,z5,z6])],[(0,[z1,z2,z3,z24,z5,z66,z6]),(0,[z0,z1,z2,z3,z5,z67,z30]),(0,[z91,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z92,z5,z6]),(0,[z0,z1,z2,z3,z5,z14,z77])],[(0,[z0,z1,z2,z3,z5,z93,z6]),(0,[z94,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z95,z6]),(0,[z0,z1,z2,z41,z78,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z96]),(0,[z0,z97,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z48,z5,z6])],[(0,[z16,z0,z1,z2,z3,z5,z98]),(0,[z99,z0,z1,z2,z3,z5,z100]),(0,[z0,z101,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z102,z5,z6]),(0,[z0,z1,z2,z3,z5,z103,z6]),(0,[z0,z104,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z68,z3,z26])],[(0,[z0,z105,z1,z2,z3,z5,z6]),(1,[z0,z106,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z107,z30]),(0,[z108,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z109,z6]),(0,[z0,z1,z2,z3,z110,z5,z6]),(0,[z111,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z112,z5,z11,z6])],[(0,[z0,z1,z2,z3,z113,z5,z6]),(1,[z0,z1,z2,z3,z5,z114]),(0,[z0,z115,z1,z2,z3,z5,z6])],[(0,[z16,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z6,z116]),(0,[z0,z1,z2,z117,z3,z5,z6]),(0,[z0,z1,z2,z3,z26,z5,z30]),(0,[z118,z0,z1,z2,z3,z5,z6])],[(0,[z0,z101,z1,z2,z78,z5,z6]),(0,[z0,z101,z2,z119,z3,z5,z6]),(0,[z60,z0,z1,z2,z3,z5,z6])],[(0,[z120,z1,z17,z2,z3,z5,z6]),(0,[z121,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z122,z6]),(0,[z123,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z124,z6]),(0,[z0,z1,z2,z3,z5,z6,z125]),(0,[z0,z126,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z127,z5,z79,z6]),(0,[z128,z0,z1,z2,z5,z6,z27]),(0,[z0,z1,z2,z3,z129,z5,z6]),(0,[z0,z1,z2,z130,z3,z5,z6])],[(0,[z131,z0,z1,z2,z3,z5,z6]),(0,[z132,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z133,z3,z5,z6]),(0,[z42,z0,z1,z35,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z30]),(0,[z0,z1,z2,z3,z5,z6,z134])],[(0,[z0,z17,z2,z54,z3,z5,z6]),(0,[z0,z1,z2,z3,z135,z5,z6]),(0,[z0,z1,z136,z44,z2,z5,z6]),(0,[z60,z0,z1,z137,z3,z5,z6]),(0,[z42,z0,z1,z2,z3,z5,z77]),(0,[z0,z138,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z139])],[(0,[z0,z1,z140,z2,z3,z5,z6]),(0,[z16,z19,z1,z2,z3,z5,z6]),(0,[z128,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z141,z5,z6]),(1,[z56,z0,z2,z3,z34,z6])],[(0,[z19,z0,z1,z2,z3,z5,z142]),(0,[z0,z1,z2,z48,z5,z79,z6]),(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z65,z5,z31,z6]),(0,[z0,z1,z2,z3,z5,z144,z6]),(0,[z0,z1,z2,z3,z145,z5,z6])],[(0,[z146,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z147,z5,z6]),(0,[z0,z1,z2,z3,z148,z5,z6]),(0,[z149,z0,z1,z2,z3,z5,z29]),(0,[z150,z151,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z13,z3,z5,z58])],[(0,[z152,z0,z1,z2,z3,z5,z67]),(0,[z153,z0,z1,z2,z3,z5,z6]),(0,[z154,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z35,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z5,z6,z155]),(0,[z156,z0,z1,z2,z119,z5,z6]),(0,[z0,z157,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z158,z6]),(1,[z0,z159,z2,z3,z5,z6]),(0,[z42,z0,z1,z2,z13,z3,z5]),(0,[z0,z1,z2,z160,z3,z5,z6]),(0,[z0,z1,z2,z3,z76,z5,z6])],[(0,[z161,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z162,z5,z6]),(0,[z0,z1,z2,z163,z3,z5,z6]),(0,[z0,z1,z2,z3,z164,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z165]),(0,[z0,z1,z2,z3,z166,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z66,z31,z6]),(0,[z167,z0,z1,z2,z3,z5,z6]),(0,[z0,z168,z1,z2,z3,z34,z6]),(0,[z0,z1,z2,z169,z3,z5,z6])],[(0,[z170,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z1,z2,z171,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z30,z77]),(0,[z0,z10,z9,z2,z3,z5,z6]),(0,[z0,z1,z44,z2,z3,z31,z6]),(0,[z0,z1,z2,z68,z3,z31,z6]),(0,[z0,z1,z44,z2,z3,z65,z6]),(0,[z0,z1,z2,z68,z3,z65,z6])],[(0,[z172,z0,z1,z2,z3,z5,z30]),(0,[z173,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z174,z6]),(0,[z0,z1,z2,z3,z5,z175,z6])],[(0,[z176,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z98]),(0,[z0,z1,z2,z3,z5,z177,z6]),(0,[z0,z1,z2,z3,z5,z178,z6]),(0,[z0,z1,z2,z3,z5,z6,z179]),(0,[z180,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z181,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z182,z6]),(0,[z0,z1,z2,z3,z5,z31,z6]),(0,[z0,z1,z2,z13,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z183])],[(0,[z0,z1,z184,z2,z3,z5,z6]),(0,[z185,z0,z1,z2,z3,z5,z6]),(0,[z150,z0,z2,z3,z5,z6,z58]),(0,[z186,z0,z1,z2,z3,z5,z6]),(0,[z187,z0,z1,z2,z3,z5,z6])],[(0,[z188,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z189,z2,z3,z5,z6]),(0,[z120,z1,z2,z3,z24,z5,z6]),(0,[z190,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z191,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z82,z6]),(0,[z0,z1,z2,z3,z5,z6,z192])]],
   [[(1,[z0,z193,z2,z3,z5,z6]),(0,[z0,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z194,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z67,z58])],[(0,[z195,z0,z1,z2,z3,z5,z6]),(0,[z0,z196,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z197,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z198]),(0,[z199,z0,z1,z2,z3,z5,z6]),(0,[z0,z200,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z63]),(0,[z0,z1,z2,z3,z201,z5,z6])],[(0,[z202,z0,z168,z2,z3,z5,z6]),(0,[z0,z101,z1,z2,z46,z5,z6]),(0,[z203,z0,z1,z2,z3,z5,z6]),(0,[z56,z0,z168,z2,z3,z5,z6])],[(0,[z74,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z204,z6]),(0,[z0,z1,z2,z3,z5,z6,z205]),(0,[z0,z1,z2,z3,z5,z6,z206])],[(0,[z121,z0,z1,z20,z3,z5,z6]),(0,[z0,z10,z2,z54,z3,z5,z6]),(0,[z207,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z11,z6]),(0,[z0,z1,z2,z13,z3,z5,z11])],[(0,[z19,z1,z2,z3,z5,z6,z30]),(0,[z0,z1,z2,z3,z86,z5,z6]),(0,[z0,z1,z208,z2,z3,z5,z6]),(0,[z209,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z210,z3,z5,z6])],[(1,[z149,z1,z2,z48,z5,z6]),(0,[z0,z1,z2,z3,z5,z66,z6]),(0,[z0,z1,z2,z3,z78,z5,z67]),(0,[z0,z1,z211,z2,z3,z5,z6]),(0,[z0,z1,z2,z53,z119,z5,z6]),(0,[z0,z168,z1,z2,z3,z110,z6]),(0,[z0,z1,z2,z3,z26,z5,z58]),(0,[z0,z1,z2,z3,z5,z6,z212]),(0,[z0,z1,z2,z213,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z214]),(0,[z21,z0,z85,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z6]),(0,[z215,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z79,z30]),(0,[z0,z1,z216,z2,z3,z5,z6]),(0,[z0,z1,z2,z41,z127,z5,z6]),(0,[z42,z0,z1,z2,z217,z5,z6]),(0,[z0,z1,z2,z13,z3,z5,z14])],[(0,[z218,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z46,z3,z5,z30]),(0,[z8,z0,z1,z2,z3,z219,z6]),(0,[z0,z101,z1,z2,z62,z5,z6]),(0,[z220,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z40,z5,z6]),(0,[z221,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z35,z3,z5,z222]),(0,[z0,z1,z2,z223,z3,z5,z6])],[(0,[z224,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z225,z6]),(0,[z0,z1,z226,z2,z3,z5,z6]),(0,[z0,z1,z35,z2,z3,z5,z222]),(0,[z0,z1,z2,z13,z3,z5,z27])],[(0,[z227,z0,z1,z2,z3,z5,z6]),(0,[z0,z101,z1,z2,z3,z5,z6]),(0,[z0,z1,z228,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z58]),(0,[z50,z0,z1,z2,z3,z5,z6]),(0,[z229,z0,z1,z2,z3,z5,z6])],[(0,[z149,z16,z1,z2,z3,z5,z6]),(0,[z230,z0,z1,z2,z3,z5,z6]),(1,[z0,z168,z2,z3,z110,z6]),(0,[z231,z0,z1,z2,z3,z5,z6])],[(1,[z99,z1,z2,z46,z5,z6]),(0,[z8,z0,z1,z2,z3,z5,z103]),(0,[z0,z1,z2,z232,z3,z5,z6]),(0,[z0,z233,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z234,z5,z6])],[(0,[z16,z0,z1,z2,z3,z5,z6]),(0,[z235,z0,z1,z2,z3,z5,z6]),(0,[z236,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z237,z5,z6]),(0,[z238,z0,z1,z2,z3,z5,z6]),(0,[z239,z0,z1,z2,z3,z5,z6]),(0,[z0,z101,z1,z2,z127,z5,z6]),(0,[z0,z1,z2,z3,z26,z5,z6])],[(0,[z202,z0,z1,z2,z3,z5,z67]),(0,[z121,z0,z1,z2,z3,z5,z30]),(0,[z156,z0,z1,z2,z48,z5,z6]),(0,[z99,z0,z1,z2,z3,z5,z240]),(0,[z0,z1,z241,z2,z3,z5,z67]),(1,[z0,z1,z57,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z242,z6]),(1,[z243,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z244,z5,z6])],[(0,[z121,z0,z193,z2,z3,z5,z6]),(0,[z245,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z11])],[(0,[z0,z1,z2,z3,z5,z6,z246]),(0,[z1,z2,z3,z24,z5,z6,z30]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z136,z2,z3,z5,z67])],[(0,[z0,z1,z2,z3,z247,z5,z6]),(0,[z0,z248,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z225]),(0,[z0,z1,z2,z3,z5,z6,z249])],[(0,[z0,z1,z2,z250,z3,z5,z6]),(0,[z0,z1,z136,z3,z41,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z64]),(1,[z0,z1,z2,z3,z5,z29]),(0,[z0,z1,z2,z3,z251,z5,z6]),(0,[z1,z2,z3,z5,z67,z6,z30]),(0,[z0,z1,z2,z53,z5,z6,z27]),(0,[z0,z1,z2,z3,z252,z5,z6]),(0,[z0,z1,z2,z253,z3,z5,z6])],[(0,[z121,z19,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z27]),(0,[z0,z254,z1,z2,z3,z5,z6])],[(1,[z1,z17,z2,z3,z5,z30]),(0,[z0,z1,z2,z255,z3,z5,z6]),(0,[z0,z1,z44,z2,z3,z5,z30]),(0,[z0,z1,z2,z68,z3,z5,z30]),(0,[z56,z190,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z256,z6]),(0,[z0,z1,z2,z257,z3,z5,z6]),(0,[z0,z1,z136,z2,z5,z79,z6]),(0,[z0,z1,z2,z3,z258,z5,z6])]],
   [[(0,[z0,z1,z2,z259,z3,z5,z6]),(0,[z21,z0,z1,z2,z237,z5,z6]),(0,[z260,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z261,z3,z5,z6]),(1,[z0,z1,z2,z33,z5,z6]),(0,[z0,z1,z137,z2,z3,z65,z6]),(0,[z0,z262,z1,z2,z3,z5,z6]),(0,[z263,z0,z1,z2,z3,z5,z6]),(0,[z264,z0,z1,z2,z3,z5,z6])],[(0,[z149,z1,z17,z2,z3,z5,z6]),(0,[z0,z1,z2,z265,z3,z5,z67]),(0,[z0,z1,z2,z3,z266,z5,z6]),(0,[z0,z1,z2,z3,z5,z267,z6]),(0,[z0,z9,z1,z54,z3,z5,z6]),(0,[z0,z1,z2,z3,z268,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z269])],[(0,[z0,z168,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z53,z3,z5,z67]),(0,[z0,z1,z2,z3,z26,z5,z14]),(1,[z0,z1,z2,z270,z5,z6])],[(0,[z271,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z272,z2,z3,z5,z6]),(0,[z273,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z274,z3,z5,z6]),(0,[z0,z275,z1,z2,z3,z5,z67]),(0,[z0,z1,z44,z2,z78,z5,z6]),(0,[z276,z0,z1,z2,z3,z5,z6])],[(0,[z277,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z278,z6]),(0,[z172,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z211,z2,z5,z6])],[],[(0,[z0,z1,z2,z3,z279,z5,z6]),(0,[z0,z1,z2,z3,z26,z76,z5])],[(0,[z280,z0,z1,z2,z3,z5,z6]),(0,[z21,z1,z2,z3,z5,z6,z30]),(0,[z0,z1,z2,z3,z65,z24,z6]),(0,[z0,z1,z281,z2,z3,z5,z6]),(0,[z282,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z53,z13,z5,z6]),(0,[z0,z283,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z284,z5,z6]),(0,[z0,z1,z2,z3,z5,z30,z285]),(0,[z0,z1,z2,z3,z5,z6,z114]),(0,[z0,z2,z119,z3,z78,z5,z6]),(0,[z50,z0,z1,z2,z3,z41,z5]),(0,[z0,z1,z2,z3,z5,z6,z27])],[(0,[z156,z202,z0,z2,z3,z5,z6]),(0,[z0,z9,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z286,z5,z6])],[(0,[z120,z0,z1,z2,z3,z24,z6]),(0,[z287,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z13,z41,z5,z6])],[(0,[z288,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z289,z6]),(0,[z0,z1,z2,z3,z290,z5,z6]),(1,[z215,z0,z1,z53,z5,z6]),(0,[z291,z0,z1,z2,z3,z5,z6])],[(0,[z292,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z293,z6])],[(0,[z42,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z211,z2,z54,z5,z6]),(1,[z0,z1,z2,z294,z5,z6]),(0,[z295,z0,z1,z2,z3,z5,z6])],[(0,[z296,z0,z1,z2,z3,z5,z6]),(1,[z297,z0,z2,z3,z5,z6]),(0,[z21,z0,z1,z49,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z11,z30]),(0,[z0,z1,z216,z2,z54,z5,z6]),(0,[z0,z1,z2,z3,z5,z298,z6]),(0,[z0,z1,z241,z3,z5,z31,z6]),(0,[z0,z1,z2,z3,z5,z58,z77]),(0,[z0,z1,z2,z3,z76,z5,z77])],[(0,[z16,z1,z2,z265,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z299,z6]),(0,[z149,z0,z1,z2,z48,z5,z6]),(0,[z0,z1,z300,z2,z3,z5,z6]),(0,[z0,z1,z44,z2,z3,z79,z6])]],
   [[(1,[z23,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z127,z5,z67]),(0,[z0,z1,z2,z301,z3,z5,z6]),(0,[z0,z9,z1,z241,z3,z5,z6]),(0,[z0,z302,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z303]),(0,[z0,z1,z137,z2,z304,z5,z6]),(0,[z305,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z306,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z307]),(0,[z0,z1,z2,z3,z5,z308,z6]),(0,[z0,z1,z265,z3,z5,z31,z6]),(0,[z0,z1,z2,z3,z5,z309,z30]),(0,[z0,z1,z2,z310,z3,z5,z6])],[(0,[z16,z120,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z24,z5,z67]),(0,[z0,z1,z2,z3,z5,z30,z311]),(0,[z0,z1,z2,z312,z3,z5,z30]),(0,[z0,z1,z313,z2,z3,z5,z6]),(0,[z0,z1,z2,z314,z3,z5,z6]),(0,[z215,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z79,z6])],[(0,[z0,z1,z2,z315,z3,z5,z6]),(0,[z0,z1,z2,z46,z3,z5,z6]),(0,[z0,z1,z2,z3,z316,z5,z6]),(0,[z0,z1,z2,z3,z5,z317,z6]),(0,[z0,z1,z2,z3,z5,z6,z318])],[(0,[z0,z319,z1,z2,z3,z5,z6]),(0,[z19,z0,z1,z2,z3,z5,z6]),(0,[z21,z23,z1,z2,z3,z5,z6]),(0,[z0,z320,z1,z2,z3,z5,z6])],[(0,[z152,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z35,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z67,z321]),(0,[z322,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z323,z5,z6]),(0,[z0,z1,z2,z3,z5,z324,z6]),(0,[z0,z1,z2,z325,z3,z5,z6])],[(0,[z326,z0,z1,z2,z3,z5,z6]),(0,[z327,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z22]),(0,[z0,z1,z2,z3,z328,z5,z6]),(0,[z0,z1,z2,z3,z329,z5,z6])],[(0,[z0,z1,z2,z3,z330,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z67]),(0,[z331,z0,z1,z2,z3,z5,z6]),(0,[z156,z0,z1,z136,z2,z5,z6]),(0,[z332,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z137,z3,z65,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z98]),(0,[z333,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z119,z3,z5,z67]),(0,[z0,z101,z1,z2,z3,z5,z198]),(0,[z56,z0,z1,z2,z3,z34,z6]),(0,[z0,z1,z2,z3,z5,z334,z6]),(0,[z215,z0,z1,z2,z3,z82,z6]),(0,[z0,z335,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z270,z3,z5,z6])],[(0,[z0,z1,z44,z2,z46,z5,z6])],[(0,[z42,z233,z1,z2,z3,z5,z6]),(0,[z42,z128,z0,z1,z2,z3,z5]),(0,[z0,z1,z35,z2,z3,z26,z5]),(0,[z0,z1,z2,z3,z336,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z337])],[(0,[z202,z152,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z338,z5,z6]),(0,[z339,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z340]),(0,[z8,z0,z1,z2,z133,z5,z6]),(0,[z0,z1,z2,z13,z5,z14,z6])],[(0,[z0,z1,z341,z2,z3,z5,z6]),(0,[z0,z1,z2,z119,z5,z79,z6]),(0,[z0,z1,z2,z3,z342,z5,z6]),(0,[z0,z1,z2,z3,z5,z343,z6]),(1,[z0,z1,z2,z3,z164,z6])],[(0,[z21,z1,z2,z3,z5,z66,z6]),(0,[z344,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z345,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z346,z5,z6])],[(0,[z0,z1,z2,z3,z5,z347,z6]),(0,[z0,z348,z1,z2,z3,z5,z6]),(0,[z0,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z349,z5,z67]),(0,[z0,z1,z2,z3,z5,z6,z321]),(0,[z0,z1,z2,z62,z3,z65,z6]),(0,[z0,z1,z44,z2,z62,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z63]),(0,[z0,z1,z2,z3,z5,z350,z6])]],
   [[(0,[z149,z99,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z77]),(1,[z0,z1,z2,z3,z219,z6]),(1,[z151,z1,z2,z3,z5,z6]),(0,[z0,z1,z351,z2,z3,z5,z6]),(0,[z0,z1,z352,z2,z3,z5,z6])],[(0,[z353,z0,z1,z2,z3,z5,z6]),(0,[z56,z0,z1,z2,z354,z5,z6]),(0,[z0,z1,z355,z2,z3,z5,z6]),(0,[z42,z0,z1,z2,z3,z5,z222]),(0,[z0,z1,z44,z2,z3,z5,z6]),(0,[z0,z1,z2,z76,z5,z144,z6]),(0,[z0,z1,z2,z68,z3,z5,z6])],[(0,[z356,z0,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z2,z3,z357,z6]),(0,[z0,z1,z137,z54,z3,z5,z6])],[(0,[z0,z9,z241,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z34,z31,z6]),(0,[z128,z0,z1,z2,z13,z5,z6])],[(0,[z0,z1,z2,z3,z5,z358,z6]),(1,[z0,z1,z2,z3,z5,z103]),(1,[z207,z1,z2,z3,z5,z6]),(0,[z0,z359,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z360]),(0,[z0,z1,z2,z3,z5,z361,z6]),(0,[z0,z1,z44,z2,z127,z5,z6]),(0,[z0,z1,z2,z3,z362,z5,z6])],[(0,[z0,z1,z2,z363,z3,z5,z6]),(0,[z0,z1,z2,z364,z3,z5,z6]),(0,[z0,z1,z44,z2,z3,z127,z6])],[(0,[z0,z168,z17,z2,z3,z5,z6]),(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z365,z6]),(0,[z0,z1,z2,z3,z78,z5,z30]),(0,[z8,z230,z1,z2,z3,z5,z6]),(0,[z0,z1,z366,z2,z3,z5,z6]),(1,[z0,z1,z367,z2,z5,z6]),(0,[z368,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z369])],[(0,[z0,z1,z370,z2,z3,z5,z6]),(0,[z56,z0,z1,z2,z3,z110,z6]),(0,[z0,z1,z2,z3,z76,z6,z77])]],
   [[(0,[z0,z1,z2,z3,z5,z240,z6]),(0,[z21,z0,z248,z2,z3,z5,z6]),(0,[z0,z2,z3,z110,z5,z34,z6])],[(0,[z150,z0,z1,z2,z3,z5,z67]),(0,[z371,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z372,z3,z5,z6])],[(0,[z0,z1,z137,z2,z3,z5,z67]),(1,[z42,z0,z1,z3,z5,z43])],[(0,[z19,z0,z1,z20,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z373])],[(0,[z152,z0,z1,z2,z3,z5,z374]),(0,[z0,z1,z2,z3,z5,z6,z375]),(0,[z0,z1,z2,z376,z3,z5,z6]),(0,[z0,z1,z2,z3,z377,z5,z6]),(0,[z0,z1,z2,z3,z378,z5,z6]),(0,[z0,z1,z2,z379,z3,z5,z6])],[(0,[z0,z1,z380,z2,z3,z5,z6]),(0,[z381,z1,z2,z3,z5,z6,z30]),(0,[z0,z1,z2,z3,z382,z5,z6]),(0,[z0,z1,z2,z3,z383,z5,z6]),(0,[z128,z0,z1,z2,z3,z5,z58]),(0,[z0,z1,z2,z3,z5,z6,z384])],[(0,[z0,z1,z2,z3,z5,z385,z6]),(0,[z120,z0,z1,z2,z3,z5,z242]),(1,[z120,z1,z2,z3,z24,z6]),(0,[z0,z1,z241,z2,z3,z5,z30]),(0,[z386,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z387,z3,z5,z67]),(0,[z0,z1,z2,z388,z3,z5,z67]),(0,[z0,z2,z54,z3,z5,z6,z58]),(1,[z0,z1,z2,z5,z389,z6])],[(0,[z99,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z5,z390,z6]),(0,[z0,z1,z2,z3,z5,z391,z67]),(0,[z156,z0,z1,z2,z5,z6,z27]),(0,[z42,z0,z1,z2,z392,z5,z6]),(0,[z393,z1,z2,z3,z26,z5,z6])]],
   [[],[(0,[z394,z0,z1,z2,z3,z5,z6]),(0,[z1,z20,z2,z265,z3,z5,z6]),(0,[z0,z1,z137,z241,z3,z5,z6]),(1,[z190,z1,z2,z3,z5,z6]),(0,[z0,z1,z136,z2,z53,z5,z6])],[(0,[z202,z0,z2,z119,z3,z5,z6]),(1,[z0,z1,z2,z259,z5,z6]),(0,[z121,z1,z2,z265,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z142,z6]),(0,[z395,z0,z1,z2,z54,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z396]),(0,[z0,z1,z2,z3,z397,z5,z6]),(0,[z398,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z399,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z41,z5,z67]),(0,[z56,z359,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z400,z3,z5,z6])],[(0,[z149,z1,z2,z3,z48,z5,z6]),(1,[z0,z1,z2,z3,z5,z240]),(0,[z0,z1,z2,z312,z3,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z401,z5,z6]),(0,[z128,z0,z1,z2,z3,z5,z6]),(0,[z0,z402,z1,z2,z3,z5,z6])],[(1,[z16,z1,z2,z3,z5,z30]),(0,[z19,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z403,z5,z6]),(0,[z8,z0,z1,z54,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z404])],[(1,[z0,z1,z2,z3,z5,z242]),(0,[z405,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z304,z3,z5,z6]),(0,[z0,z1,z2,z3,z244,z65,z5]),(0,[z0,z1,z2,z3,z5,z6,z406])],[(0,[z152,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z407,z3,z5,z6]),(0,[z0,z1,z408,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z409,z5,z6]),(0,[z0,z1,z35,z2,z3,z5,z6]),(0,[z410,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z411,z6])]],
   [[(0,[z215,z0,z1,z2,z41,z5,z6]),(0,[z0,z1,z2,z412,z3,z5,z6])],[(0,[z413,z0,z1,z2,z3,z5,z6]),(0,[z0,z168,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z53,z3,z5,z30]),(0,[z0,z1,z414,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z13,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z415])],[(0,[z152,z0,z1,z2,z3,z5,z64]),(0,[z416,z0,z1,z2,z3,z5,z6]),(0,[z149,z0,z1,z2,z3,z5,z417]),(0,[z381,z23,z1,z2,z3,z5,z6]),(1,[z381,z1,z2,z3,z5,z30]),(0,[z56,z0,z1,z2,z3,z5,z67])],[(0,[z0,z1,z2,z3,z5,z418,z6]),(0,[z21,z0,z1,z2,z3,z66,z6]),(0,[z0,z1,z2,z3,z419,z5,z67]),(0,[z0,z1,z2,z3,z5,z58,z43]),(0,[z420,z0,z1,z2,z3,z5,z6]),(0,[z421,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z422,z6]),(0,[z0,z1,z2,z3,z65,z5,z423]),(0,[z0,z1,z2,z3,z5,z6,z424])],[(0,[z425,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z147,z5,z6]),(0,[z426,z0,z1,z2,z3,z5,z6])],[(0,[z99,z0,z1,z2,z46,z5,z6]),(0,[z381,z0,z1,z2,z3,z5,z67]),(0,[z8,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z427,z54,z3,z5]),(0,[z0,z1,z2,z53,z78,z5,z6]),(0,[z0,z1,z428,z2,z3,z5,z6]),(0,[z128,z0,z1,z2,z3,z5,z11]),(0,[z429,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z62,z53,z5,z6])],[(1,[z0,z1,z2,z430,z5,z6]),(0,[z23,z0,z1,z2,z3,z5,z67]),(0,[z0,z431,z1,z2,z3,z5,z6])],[(0,[z432,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z433,z2,z3,z5,z6]),(1,[z0,z1,z2,z112,z5,z6]),(0,[z128,z0,z1,z35,z2,z3,z5]),(0,[z0,z1,z2,z3,z26,z6,z77])]],
   [[(0,[z434,z0,z1,z2,z3,z5,z6]),(0,[z435,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z436,z5,z6]),(0,[z0,z9,z1,z2,z3,z5,z30]),(0,[z437,z0,z1,z2,z3,z5,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z70])],[(0,[z0,z1,z2,z3,z5,z6,z438]),(0,[z128,z0,z1,z2,z3,z5,z27])],[(0,[z0,z1,z2,z3,z439,z5,z6]),(0,[z440,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z137,z2,z3,z31,z6])],[(0,[z0,z1,z17,z2,z3,z5,z67]),(0,[z8,z0,z1,z241,z3,z5,z6])],[(0,[z152,z0,z17,z2,z3,z5,z6]),(1,[z0,z85,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z14,z67]),(0,[z0,z1,z2,z3,z441,z5,z6])],[(0,[z23,z1,z2,z3,z5,z67,z6]),(0,[z0,z1,z2,z3,z5,z442,z6]),(0,[z156,z0,z2,z3,z78,z5,z6]),(1,[z1,z32,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z443,z5,z6]),(0,[z0,z1,z2,z3,z444,z5,z6]),(0,[z0,z1,z2,z445,z3,z5,z6]),(0,[z151,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z423]),(0,[z0,z1,z2,z3,z65,z6,z77])],[(0,[z446,z0,z1,z2,z3,z5,z6]),(0,[z297,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z127,z5,z30]),(0,[z0,z1,z2,z3,z447,z5,z6]),(0,[z215,z0,z1,z53,z3,z5,z6]),(0,[z448,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z68,z3,z26,z5])]],
   [[(0,[z449,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z450,z2,z3,z5,z67]),(0,[z0,z1,z451,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z78,z5,z6]),(0,[z150,z0,z1,z2,z3,z5,z11]),(0,[z0,z1,z2,z5,z11,z6,z384]),(0,[z42,z452,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z453])],[(0,[z454,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z24,z5,z30]),(0,[z0,z1,z2,z62,z3,z5,z67]),(0,[z0,z1,z2,z3,z5,z6,z455]),(0,[z156,z215,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z222,z58]),(0,[z0,z1,z2,z3,z456,z5,z6]),(0,[z0,z1,z2,z3,z90,z5,z6])],[(0,[z0,z1,z2,z457,z3,z5,z6]),(0,[z21,z0,z1,z458,z3,z5,z6]),(0,[z459,z0,z1,z2,z3,z5,z6]),(0,[z120,z0,z1,z2,z3,z5,z73]),(0,[z460,z0,z1,z2,z3,z5,z6]),(0,[z150,z0,z1,z35,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z11,z43]),(0,[z0,z1,z2,z5,z14,z6,z27])],[(0,[z0,z1,z461,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z22]),(1,[z0,z1,z2,z133,z5,z6]),(1,[z0,z1,z2,z427,z3,z5]),(0,[z0,z1,z2,z112,z3,z5,z6]),(1,[z0,z1,z2,z392,z5,z6]),(0,[z0,z1,z2,z3,z462,z5,z6])],[(0,[z149,z0,z1,z2,z3,z5,z67]),(0,[z56,z0,z1,z163,z3,z5,z6])],[(0,[z0,z1,z2,z463,z3,z5,z6]),(0,[z121,z0,z1,z265,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z43]),(0,[z0,z1,z2,z3,z464,z5,z6]),(0,[z0,z1,z2,z3,z5,z465,z6])],[(0,[z1,z17,z2,z265,z3,z5,z6]),(0,[z0,z1,z2,z466,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z354,z3,z5,z6]),(0,[z0,z1,z3,z5,z222,z6,z43]),(0,[z0,z1,z2,z62,z5,z79,z6]),(0,[z467,z0,z1,z2,z3,z5,z6])],[(0,[z468,z0,z1,z2,z3,z5,z6]),(0,[z0,z469,z1,z2,z3,z5,z6]),(0,[z121,z0,z1,z2,z430,z5,z6]),(1,[z121,z1,z265,z3,z5,z6]),(0,[z0,z1,z2,z3,z470,z5,z6]),(0,[z0,z1,z2,z119,z3,z5,z30]),(0,[z471,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z217,z5,z6]),(0,[z0,z1,z2,z472,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z473]),(0,[z474,z0,z1,z2,z3,z5,z6]),(0,[z475,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z44,z2,z127,z6])]],
   [[(0,[z202,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z476,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z34,z67]),(0,[z0,z1,z241,z2,z3,z5,z6]),(0,[z477,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z478,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z222,z6])],[(0,[z0,z1,z2,z3,z5,z6,z285]),(0,[z0,z1,z2,z3,z479,z5,z6]),(0,[z0,z1,z2,z3,z480,z5,z6]),(1,[z0,z1,z2,z3,z5,z100]),(1,[z0,z1,z2,z3,z357,z6]),(0,[z42,z150,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z481,z6]),(0,[z0,z1,z35,z2,z3,z5,z43]),(0,[z0,z1,z2,z68,z3,z5,z77])],[(0,[z0,z1,z2,z482,z3,z5,z6]),(1,[z1,z2,z3,z5,z67,z30]),(0,[z0,z1,z2,z3,z5,z483,z6]),(1,[z0,z1,z2,z304,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z484])],[(0,[z0,z1,z2,z53,z46,z5,z6]),(0,[z8,z254,z1,z2,z3,z5,z6]),(0,[z0,z1,z136,z2,z3,z5,z6]),(0,[z485,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z399,z2,z3,z5,z30]),(0,[z0,z1,z486,z2,z3,z5,z6]),(0,[z0,z1,z2,z487,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z488])],[(0,[z0,z1,z2,z3,z489,z5,z6]),(1,[z0,z1,z2,z237,z5,z6]),(0,[z128,z0,z1,z2,z3,z5,z30]),(1,[z230,z1,z2,z3,z5,z6]),(0,[z490,z0,z1,z2,z3,z5,z6]),(0,[z215,z0,z1,z44,z2,z5,z6]),(0,[z0,z1,z367,z2,z65,z5,z6]),(0,[z0,z491,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z492,z5,z6]),(0,[z0,z1,z2,z493,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z494,z6]),(0,[z0,z1,z2,z3,z495,z5,z6]),(0,[z0,z1,z2,z41,z48,z5,z6]),(0,[z0,z1,z2,z3,z496,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z43])]],
   [[(0,[z0,z1,z2,z3,z497,z5,z6]),(0,[z0,z10,z2,z3,z5,z11,z6])],[(0,[z0,z1,z2,z3,z498,z5,z6]),(0,[z0,z1,z2,z3,z5,z499,z67]),(0,[z500,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z501,z6]),(0,[z502,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z503,z2,z3,z5,z6])],[(0,[z0,z1,z2,z265,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z417]),(0,[z99,z1,z2,z46,z3,z5,z6]),(0,[z0,z1,z2,z3,z504,z5,z6]),(0,[z0,z1,z505,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z311]),(0,[z19,z0,z1,z2,z3,z5,z70]),(0,[z0,z168,z1,z2,z3,z5,z6]),(0,[z0,z168,z2,z3,z110,z5,z6]),(0,[z0,z1,z2,z53,z3,z5,z6]),(0,[z0,z1,z2,z3,z506,z5,z6])],[(0,[z0,z1,z2,z3,z507,z5,z6]),(0,[z0,z275,z1,z2,z3,z5,z6]),(0,[z207,z101,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z508,z5,z6])],[(0,[z0,z101,z1,z2,z48,z5,z6]),(1,[z156,z0,z2,z78,z5,z6]),(0,[z509,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z510,z6]),(0,[z0,z10,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z5,z511,z6]),(0,[z0,z1,z2,z53,z127,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z512])],[(0,[z0,z1,z20,z2,z3,z5,z67]),(0,[z0,z1,z2,z513,z3,z5,z6]),(1,[z0,z101,z2,z119,z5,z6]),(0,[z0,z1,z514,z2,z3,z5,z6])]],
   [[(0,[z150,z0,z1,z2,z3,z5,z30]),(0,[z515,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z11,z77])],[(0,[z16,z1,z2,z3,z5,z66,z6]),(0,[z0,z1,z137,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z65,z5,z67]),(0,[z516,z0,z1,z2,z3,z5,z6]),(0,[z517,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z35,z3,z5,z222,z6])],[(0,[z0,z1,z2,z3,z518,z5,z6]),(0,[z0,z9,z1,z2,z3,z5,z6]),(0,[z519,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z62,z3,z31,z6]),(0,[z0,z1,z2,z65,z5,z389,z6])],[(1,[z0,z1,z49,z3,z5,z6])],[(0,[z120,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z5,z6,z520])],[(0,[z0,z1,z521,z2,z3,z5,z6]),(0,[z0,z1,z522,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z523]),(0,[z0,z1,z2,z3,z524,z5,z6])],[(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z99,z0,z1,z2,z3,z5,z30]),(0,[z525,z0,z1,z2,z3,z5,z6]),(0,[z42,z0,z1,z2,z3,z5,z6]),(0,[z0,z526,z1,z2,z3,z5,z6])],[(0,[z0,z1,z35,z2,z3,z5,z77]),(0,[z0,z1,z2,z3,z527,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z528,z5,z6]),(0,[z42,z0,z1,z2,z3,z178,z6])],[(0,[z0,z1,z2,z3,z127,z5,z6])],[(0,[z202,z0,z2,z3,z5,z34,z6]),(0,[z0,z1,z2,z3,z41,z5,z30]),(0,[z449,z0,z1,z2,z3,z5,z6]),(0,[z529,z0,z1,z2,z3,z5,z6]),(0,[z56,z0,z2,z3,z5,z34,z6])],[(0,[z0,z1,z2,z3,z24,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z294,z5,z6]),(1,[z393,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z530,z6]),(1,[z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z54,z3,z5,z67]),(0,[z0,z1,z35,z2,z13,z3,z5])],[(0,[z16,z0,z1,z2,z147,z5,z6]),(0,[z0,z1,z2,z531,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z532]),(0,[z0,z533,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z77])],[(0,[z0,z1,z2,z3,z5,z374,z6]),(0,[z0,z1,z2,z534,z3,z5,z6]),(0,[z322,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z24,z31,z6]),(0,[z0,z1,z2,z3,z5,z30,z246]),(0,[z0,z1,z535,z2,z3,z5,z6])],[(0,[z0,z1,z2,z536,z3,z5,z6]),(0,[z0,z1,z2,z537,z3,z5,z6]),(0,[z156,z0,z1,z2,z78,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z538])]],
   [[(0,[z19,z1,z17,z2,z3,z5,z6]),(0,[z0,z9,z17,z2,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z6]),(0,[z539,z0,z1,z2,z3,z5,z6])],[(0,[z202,z0,z1,z2,z3,z5,z30]),(0,[z56,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z222,z30]),(0,[z0,z1,z2,z119,z3,z5,z6]),(0,[z0,z1,z53,z3,z41,z5,z6])],[(0,[z16,z202,z0,z2,z3,z5,z6]),(0,[z150,z243,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z540]),(0,[z0,z1,z2,z541,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z84,z67]),(0,[z56,z0,z1,z2,z443,z5,z6])],[(0,[z381,z0,z1,z2,z3,z5,z30]),(0,[z8,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z136,z2,z3,z5,z30]),(0,[z0,z1,z2,z294,z5,z34,z6]),(0,[z0,z243,z1,z2,z3,z5,z6]),(0,[z0,z1,z137,z2,z496,z5,z6]),(0,[z0,z1,z2,z62,z3,z5,z139])],[(0,[z0,z1,z2,z542,z3,z5,z6]),(0,[z23,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z198,z6]),(0,[z0,z1,z543,z2,z3,z5,z6])],[(0,[z544,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z545,z3,z5,z6]),(0,[z0,z1,z20,z3,z5,z31,z6]),(0,[z546,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z77,z27])],[(1,[z0,z1,z2,z3,z5,z547]),(0,[z0,z1,z2,z3,z48,z5,z67]),(0,[z0,z1,z2,z3,z5,z6,z532]),(0,[z0,z1,z2,z3,z5,z548,z6]),(0,[z0,z1,z549,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z550,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z349,z5,z6]),(0,[z0,z551,z1,z2,z3,z5,z6]),(0,[z552,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z553,z6]),(0,[z0,z1,z2,z554,z3,z5,z6]),(0,[z0,z1,z555,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z110,z5,z67]),(1,[z233,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z139,z6])],[(0,[z202,z0,z9,z2,z3,z5,z6]),(1,[z0,z348,z2,z3,z5,z6]),(0,[z0,z1,z556,z2,z3,z5,z6]),(0,[z557,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z17,z2,z3,z5,z30]),(0,[z558,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z265,z3,z5,z30]),(0,[z0,z1,z2,z3,z559,z5,z6]),(0,[z0,z1,z560,z2,z3,z5,z6]),(0,[z150,z0,z1,z2,z3,z5,z58]),(0,[z0,z1,z2,z3,z5,z6,z561]),(0,[z0,z1,z2,z3,z5,z6,z423]),(0,[z562,z0,z1,z2,z3,z5,z6])],[(1,[z152,z17,z2,z3,z5,z6]),(0,[z23,z19,z1,z2,z3,z5,z6]),(0,[z563,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z46,z41,z5,z6]),(0,[z0,z1,z2,z3,z5,z30,z27]),(0,[z0,z1,z2,z3,z5,z14,z30]),(0,[z60,z0,z1,z2,z3,z5,z67])],[(0,[z121,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z5,z6,z564]),(1,[z0,z248,z2,z3,z5,z6]),(0,[z0,z101,z1,z136,z2,z5,z6])],[(0,[z0,z1,z2,z565,z3,z5,z6]),(0,[z0,z1,z2,z566,z3,z5,z6]),(0,[z567,z0,z1,z2,z3,z5,z6]),(0,[z132,z0,z1,z2,z3,z5,z67]),(1,[z0,z1,z163,z3,z5,z6]),(1,[z0,z1,z2,z5,z144,z6])],[(0,[z0,z1,z2,z3,z5,z219,z6]),(0,[z568,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z33,z3,z5,z6]),(0,[z42,z0,z159,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z569,z30]),(0,[z0,z1,z2,z62,z3,z5,z30]),(0,[z0,z1,z2,z570,z3,z5,z6])],[(0,[z0,z1,z2,z3,z571,z5,z6]),(0,[z572,z0,z1,z2,z3,z5,z6])],[(1,[z254,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z65,z34,z6]),(0,[z150,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z573,z6])],[(0,[z149,z0,z1,z2,z3,z5,z30]),(0,[z0,z574,z1,z2,z3,z5,z6]),(0,[z0,z1,z57,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z575,z6]),(0,[z0,z1,z137,z2,z3,z5,z6]),(0,[z128,z0,z1,z2,z3,z5,z14])],[(0,[z0,z1,z576,z2,z3,z5,z6]),(0,[z577,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z578,z3,z5,z6]),(1,[z0,z1,z2,z3,z178,z6])],[(0,[z0,z17,z2,z119,z3,z5,z6]),(0,[z156,z0,z1,z2,z46,z5,z6]),(0,[z0,z1,z2,z3,z5,z30,z307]),(0,[z0,z1,z2,z3,z76,z5,z67])],[(0,[z202,z0,z2,z54,z3,z5,z6]),(0,[z121,z0,z1,z2,z259,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z100]),(0,[z0,z1,z2,z3,z357,z5,z6])],[(0,[z386,z0,z1,z2,z3,z5,z6]),(0,[z579,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z34,z30]),(0,[z42,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z387,z3,z5,z6]),(0,[z0,z1,z2,z388,z3,z5,z6]),(0,[z0,z101,z1,z2,z119,z5,z6])]],
   [[(0,[z580,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z391,z6]),(0,[z99,z0,z1,z2,z3,z5,z6]),(0,[z120,z0,z1,z2,z3,z66,z6]),(0,[z215,z0,z101,z1,z2,z5,z6])],[(0,[z581,z0,z1,z2,z3,z5,z6]),(1,[z395,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z582,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z583]),(1,[z0,z1,z137,z3,z65,z6]),(0,[z0,z1,z584,z2,z3,z5,z6]),(0,[z585,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z586,z3,z5,z6]),(0,[z21,z0,z1,z2,z162,z5,z6]),(0,[z0,z1,z2,z587,z3,z5,z6]),(0,[z150,z0,z10,z2,z3,z5,z6]),(1,[z1,z2,z3,z90,z5,z6])],[(0,[z121,z0,z348,z2,z3,z5,z6]),(0,[z19,z0,z1,z265,z3,z5,z6]),(0,[z0,z1,z2,z3,z588,z5,z6]),(0,[z19,z1,z20,z2,z3,z5,z6]),(0,[z0,z1,z44,z2,z48,z5,z6]),(0,[z0,z1,z2,z3,z5,z31,z67]),(0,[z0,z1,z2,z13,z3,z5,z67]),(0,[z395,z0,z1,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z62,z5,z6]),(0,[z56,z0,z1,z2,z3,z5,z404]),(0,[z215,z0,z1,z136,z3,z5,z6]),(0,[z0,z1,z2,z589,z3,z5,z6]),(0,[z0,z1,z2,z590,z3,z5,z6])],[(0,[z21,z120,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z382,z5,z6]),(0,[z0,z1,z2,z591,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z25]),(1,[z0,z1,z2,z5,z6,z384]),(0,[z0,z1,z2,z3,z41,z5,z6]),(0,[z215,z0,z1,z2,z3,z573,z6]),(0,[z0,z1,z2,z3,z5,z389,z6]),(0,[z42,z0,z1,z2,z3,z26,z5]),(0,[z592,z0,z1,z2,z3,z5,z6])],[(0,[z16,z1,z2,z3,z5,z6,z30]),(1,[z0,z1,z2,z3,z5,z142]),(0,[z593,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z594,z3,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z6]),(0,[z56,z0,z1,z2,z3,z5,z575])],[(0,[z0,z1,z595,z2,z3,z5,z6]),(0,[z596,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z597,z5,z6]),(0,[z0,z1,z2,z3,z31,z6,z77])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z148,z6]),(0,[z0,z1,z2,z3,z5,z6,z417]),(0,[z0,z1,z2,z3,z5,z30,z30]),(0,[z0,z1,z2,z41,z5,z6,z27]),(0,[z0,z1,z598,z2,z3,z5,z6]),(0,[z0,z1,z2,z599,z3,z5,z6])]],
   [[(0,[z0,z1,z600,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z127,z5,z6]),(0,[z0,z1,z2,z62,z3,z79,z6]),(0,[z0,z1,z2,z13,z5,z79,z6]),(0,[z0,z1,z2,z270,z76,z5,z6])],[(0,[z0,z1,z2,z3,z601,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z155]),(0,[z0,z1,z2,z3,z65,z110,z6]),(0,[z0,z1,z602,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z603,z5,z6]),(0,[z0,z1,z2,z3,z5,z604,z6]),(0,[z0,z1,z2,z3,z5,z6,z107]),(0,[z0,z1,z2,z3,z110,z31,z6]),(0,[z605,z0,z1,z2,z3,z5,z6])],[(0,[z152,z1,z17,z2,z3,z5,z6]),(0,[z16,z202,z1,z2,z3,z5,z6]),(0,[z0,z1,z606,z2,z3,z5,z6]),(0,[z74,z0,z1,z2,z3,z5,z67]),(0,[z156,z0,z101,z2,z3,z5,z6]),(0,[z56,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z607]),(0,[z0,z1,z2,z608,z3,z5,z6]),(0,[z60,z0,z1,z3,z5,z31,z6]),(1,[z0,z1,z2,z3,z244,z5]),(0,[z0,z1,z2,z3,z609,z5,z6])],[(0,[z0,z1,z2,z3,z419,z5,z6]),(0,[z0,z1,z2,z610,z3,z5,z6]),(0,[z0,z1,z2,z3,z611,z5,z6])],[(0,[z0,z1,z2,z3,z5,z612,z6]),(0,[z99,z0,z106,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z73]),(0,[z0,z10,z1,z2,z3,z5,z30]),(0,[z0,z101,z1,z2,z5,z6,z27]),(0,[z0,z1,z2,z613,z3,z5,z6]),(0,[z60,z0,z1,z2,z3,z65,z6]),(0,[z60,z0,z1,z2,z3,z31,z6])],[(0,[z614,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z20,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z66,z67]),(0,[z381,z0,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z427,z3,z5,z6]),(0,[z615,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z354,z5,z6]),(0,[z0,z159,z1,z2,z3,z5,z6]),(0,[z0,z616,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z617,z3,z5,z6]),(0,[z23,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z67]),(0,[z0,z1,z2,z119,z41,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z618]),(0,[z0,z1,z2,z619,z3,z5,z6]),(0,[z0,z1,z88,z2,z3,z5,z6]),(0,[z42,z0,z1,z3,z5,z6,z43])]],
   [[(0,[z0,z1,z620,z2,z3,z5,z6]),(0,[z0,z1,z2,z621,z3,z5,z6]),(0,[z0,z1,z2,z162,z3,z5,z6]),(0,[z0,z1,z2,z3,z65,z5,z30]),(0,[z0,z1,z2,z3,z622,z5,z6])],[(0,[z0,z1,z2,z623,z3,z5,z6]),(0,[z0,z1,z2,z624,z3,z5,z6]),(0,[z0,z1,z2,z3,z625,z5,z6]),(0,[z0,z1,z2,z5,z79,z6,z27]),(0,[z0,z1,z626,z2,z3,z5,z6])],[(0,[z16,z23,z1,z2,z3,z5,z6]),(0,[z0,z1,z137,z20,z3,z5,z6]),(0,[z0,z101,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z627,z5,z6]),(0,[z0,z1,z2,z3,z5,z628,z6])],[(0,[z156,z0,z17,z2,z3,z5,z6]),(0,[z629,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z630,z2,z3,z5,z6]),(0,[z120,z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z67,z631]),(0,[z0,z1,z2,z3,z632,z5,z6]),(0,[z0,z1,z2,z3,z633,z5,z6])],[(0,[z0,z1,z2,z3,z430,z5,z6]),(0,[z0,z1,z106,z2,z3,z5,z6])],[(0,[z0,z1,z17,z2,z3,z5,z6]),(0,[z16,z0,z1,z2,z3,z5,z67]),(0,[z634,z0,z1,z2,z3,z5,z6]),(0,[z149,z0,z1,z2,z46,z5,z6]),(0,[z0,z1,z2,z3,z26,z5,z67]),(0,[z0,z1,z2,z3,z635,z5,z6])],[(0,[z0,z1,z2,z636,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z14,z6])],[(0,[z16,z152,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z116]),(1,[z0,z1,z458,z3,z5,z6]),(0,[z0,z101,z1,z2,z13,z5,z6]),(0,[z637,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z17,z2,z3,z5,z66,z6]),(0,[z16,z0,z1,z2,z536,z5,z6]),(0,[z121,z0,z1,z2,z3,z148,z6]),(0,[z8,z0,z1,z2,z382,z5,z6]),(0,[z638,z0,z1,z2,z3,z5,z6]),(0,[z639,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z640])],[(0,[z0,z1,z2,z3,z641,z5,z6]),(0,[z297,z99,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z38,z3,z5,z30]),(0,[z0,z1,z450,z2,z3,z5,z6])],[(0,[z0,z1,z2,z642,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z569,z6]),(0,[z0,z643,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z644,z3,z5,z6]),(0,[z0,z1,z2,z3,z645,z5,z6]),(0,[z0,z1,z646,z2,z3,z5,z6]),(0,[z0,z1,z647,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z648,z6]),(0,[z0,z1,z2,z62,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z54,z3,z5,z30]),(0,[z0,z1,z2,z649,z3,z5,z6]),(0,[z0,z1,z2,z3,z650,z5,z6])],[(0,[z0,z1,z651,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z652]),(0,[z653,z0,z1,z2,z3,z5,z6]),(0,[z8,z0,z1,z2,z3,z5,z114]),(0,[z654,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z18,z6]),(0,[z149,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z631]),(1,[z0,z1,z2,z443,z5,z6]),(0,[z655,z0,z1,z2,z3,z5,z6])],[(0,[z656,z0,z1,z2,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z225]),(0,[z0,z1,z2,z3,z5,z657,z6]),(0,[z658,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z659,z2,z3,z5,z6]),(0,[z0,z1,z2,z62,z3,z127,z6])],[(0,[z0,z1,z2,z3,z660,z5,z6]),(0,[z0,z1,z2,z3,z5,z661,z6]),(1,[z0,z1,z136,z41,z5,z6]),(1,[z452,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z662])]],
   [[(0,[z16,z0,z1,z2,z3,z5,z547]),(1,[z359,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z11,z222])],[(0,[z663,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z34,z6]),(1,[z0,z1,z2,z3,z40,z5])],[(0,[z0,z1,z2,z664,z3,z5,z6]),(0,[z665,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z30,z58]),(0,[z0,z1,z2,z3,z5,z666,z6]),(0,[z0,z241,z2,z54,z3,z5,z6]),(0,[z42,z0,z10,z1,z2,z3,z5]),(0,[z667,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z668,z5,z6]),(0,[z0,z1,z2,z3,z5,z67,z222]),(1,[z8,z0,z54,z3,z5,z6]),(0,[z669,z0,z1,z2,z3,z5,z6]),(0,[z670,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z671,z6]),(0,[z0,z1,z2,z3,z5,z672,z6])],[(0,[z202,z1,z17,z2,z3,z5,z6]),(0,[z0,z673,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z573,z5,z6]),(0,[z0,z1,z2,z392,z3,z5,z6]),(0,[z0,z674,z1,z2,z3,z5,z6])],[(0,[z0,z1,z675,z2,z3,z5,z6]),(0,[z215,z0,z1,z2,z53,z5,z6]),(0,[z0,z1,z2,z3,z217,z5,z6])],[(0,[z676,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z48,z5,z30]),(0,[z0,z1,z2,z3,z5,z677,z6]),(0,[z0,z1,z678,z2,z3,z5,z6])],[(0,[z99,z0,z1,z2,z48,z5,z6]),(1,[z21,z1,z2,z3,z66,z6]),(0,[z0,z1,z2,z3,z5,z679,z6]),(0,[z680,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z23,z1,z17,z2,z3,z5,z6]),(0,[z121,z0,z1,z2,z3,z5,z116]),(0,[z23,z1,z2,z265,z3,z5,z6]),(0,[z0,z1,z2,z3,z110,z5,z30]),(0,[z108,z0,z1,z2,z3,z5,z30]),(1,[z150,z0,z2,z3,z5,z58]),(0,[z0,z10,z1,z2,z3,z5,z58]),(0,[z0,z681,z1,z2,z3,z5,z6])],[(0,[z0,z1,z682,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z113,z5,z30]),(0,[z42,z0,z88,z2,z3,z5,z6]),(1,[z0,z1,z2,z62,z79,z6])],[(0,[z0,z1,z2,z3,z5,z499,z6]),(1,[z0,z1,z2,z536,z5,z6]),(0,[z0,z1,z193,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z683,z5,z6]),(0,[z684,z0,z1,z2,z3,z5,z6]),(0,[z685,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z686,z5,z6]),(0,[z452,z0,z1,z2,z3,z5,z6])],[(0,[z687,z0,z1,z2,z3,z5,z6]),(0,[z60,z0,z1,z2,z3,z5,z30]),(0,[z0,z688,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z68,z3,z76,z6])],[(0,[z1,z2,z265,z3,z5,z6,z30]),(0,[z689,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z690]),(0,[z0,z1,z2,z3,z691,z5,z6])],[(0,[z123,z0,z1,z2,z3,z5,z6]),(0,[z121,z0,z1,z2,z3,z5,z652]),(1,[z0,z1,z216,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z692,z6]),(0,[z0,z1,z44,z2,z119,z5,z6])],[(0,[z121,z0,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z693,z3,z5,z6]),(0,[z0,z1,z694,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z695,z6]),(1,[z0,z1,z2,z496,z5,z6]),(0,[z0,z696,z1,z2,z3,z5,z6])],[(0,[z0,z1,z137,z265,z3,z5,z6]),(0,[z0,z1,z458,z2,z3,z5,z6]),(0,[z0,z10,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z697,z2,z3,z5,z6]),(0,[z0,z1,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z652,z6])],[(0,[z0,z1,z2,z3,z5,z6,z309]),(0,[z215,z0,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z5,z79,z67]),(0,[z0,z1,z2,z698,z3,z5,z6]),(0,[z0,z1,z2,z3,z699,z5,z6])],[(1,[z0,z1,z2,z3,z5,z374]),(0,[z0,z1,z2,z46,z3,z5,z67]),(0,[z0,z101,z1,z2,z3,z5,z25]),(0,[z0,z1,z2,z3,z65,z5,z6])],[(0,[z19,z0,z1,z2,z3,z5,z67]),(1,[z128,z0,z1,z2,z5,z27])],[(0,[z0,z1,z2,z3,z5,z700,z6]),(1,[z1,z2,z265,z3,z5,z30]),(0,[z0,z1,z2,z3,z76,z5,z30]),(0,[z0,z1,z2,z3,z5,z701,z6]),(0,[z0,z1,z2,z3,z26,z5,z11]),(0,[z0,z1,z136,z2,z41,z5,z6]),(0,[z0,z1,z2,z3,z5,z702,z6])],[(0,[z0,z17,z2,z3,z5,z34,z6]),(0,[z703,z0,z1,z2,z3,z5,z6]),(0,[z120,z0,z1,z2,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z24,z6]),(1,[z0,z1,z2,z3,z5,z404]),(0,[z393,z0,z1,z2,z3,z5,z6])],[(0,[z101,z1,z32,z2,z3,z5,z6]),(0,[z0,z1,z2,z704,z3,z5,z6]),(0,[z215,z0,z1,z2,z5,z79,z6]),(0,[z0,z1,z367,z2,z3,z5,z6]),(0,[z42,z0,z1,z2,z3,z164,z6])],[(0,[z0,z1,z2,z3,z705,z5,z6]),(0,[z0,z1,z2,z3,z5,z547,z6]),(0,[z0,z1,z2,z46,z5,z79,z6]),(1,[z0,z1,z2,z3,z5,z575]),(0,[z0,z1,z2,z3,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z5,z30,z707]),(0,[z0,z1,z2,z377,z5,z27])],[(0,[z1,z2,z3,z90,z76,z5])],[(0,[z150,z151,z2,z3,z5,z58])],[(0,[z654,z1,z2,z3,z5,z30]),(0,[z708,z1,z2,z3,z5,z6])],[(0,[z709,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z710,z3,z5]),(0,[z0,z1,z2,z3,z711,z6]),(0,[z0,z1,z2,z3,z5,z712]),(0,[z0,z1,z2,z3,z5,z713]),(0,[z0,z674,z2,z119,z5,z6]),(0,[z0,z1,z2,z443,z5,z404])],[(0,[z254,z1,z2,z3,z5,z103]),(0,[z230,z1,z2,z3,z357,z6])],[(0,[z0,z1,z2,z3,z5,z714])],[(0,[z0,z1,z2,z147,z5,z67])],[(0,[z0,z1,z2,z3,z5,z715]),(0,[z0,z1,z2,z3,z5,z716])],[(0,[z0,z1,z2,z3,z717,z6]),(0,[z0,z1,z3,z5,z718,z43])],[(0,[z0,z1,z2,z3,z5,z30]),(0,[z719,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z720,z5]),(0,[z0,z1,z2,z112,z5,z67]),(0,[z721,z1,z2,z3,z5,z6]),(0,[z8,z395,z0,z54,z3,z5])],[(0,[z0,z1,z2,z3,z5,z652]),(0,[z0,z1,z2,z722,z5,z6]),(0,[z0,z1,z2,z13,z5,z384])],[(0,[z60,z0,z1,z3,z31,z30]),(0,[z0,z1,z2,z3,z5,z723])],[(0,[z0,z1,z2,z724,z5,z6])],[(0,[z0,z1,z2,z3,z5,z725]),(0,[z0,z1,z2,z726,z5,z6]),(0,[z0,z1,z727,z41,z5,z6]),(0,[z728,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z729]),(0,[z0,z1,z2,z730,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z82,z30]),(0,[z731,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z40,z5])],[(0,[z1,z2,z3,z588,z5,z30]),(0,[z0,z1,z732,z3,z5,z6])],[(0,[z0,z526,z2,z3,z5,z58]),(0,[z0,z1,z2,z13,z5,z350])],[(0,[z0,z1,z2,z733,z5,z6]),(0,[z0,z1,z2,z3,z734,z6]),(0,[z0,z735,z2,z3,z5,z67]),(0,[z0,z1,z736,z3,z5,z6])],[],[(0,[z0,z1,z2,z3,z5,z737]),(0,[z0,z1,z2,z3,z5,z738]),(0,[z0,z1,z2,z3,z5,z739]),(0,[z156,z0,z2,z740,z5,z6]),(0,[z233,z1,z2,z13,z3,z5]),(0,[z0,z1,z35,z3,z5,z222])],[(0,[z0,z1,z2,z133,z5,z67])],[(0,[z420,z1,z2,z48,z5,z6]),(0,[z230,z1,z2,z3,z219,z6]),(0,[z395,z0,z10,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z741]),(0,[z190,z1,z2,z3,z5,z742]),(0,[z0,z1,z2,z3,z5,z743])],[(0,[z1,z2,z3,z603,z5,z30]),(0,[z0,z1,z2,z744,z5,z6]),(0,[z0,z1,z2,z3,z5,z745]),(0,[z264,z0,z1,z3,z31,z6])],[(0,[z0,z1,z35,z3,z5,z309])],[(0,[z0,z1,z2,z746,z5,z6]),(0,[z0,z248,z2,z3,z5,z225]),(0,[z0,z1,z44,z2,z127,z67]),(0,[z0,z1,z2,z217,z5,z67]),(0,[z0,z1,z747,z3,z5,z6]),(0,[z0,z1,z44,z2,z389,z6])],[(0,[z0,z1,z2,z3,z5,z748])],[(0,[z243,z1,z2,z3,z5,z6]),(0,[z749,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z62,z750,z6])],[(0,[z0,z1,z751,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z752]),(0,[z0,z1,z2,z3,z5,z753]),(0,[z0,z1,z2,z754,z5,z6]),(0,[z1,z2,z3,z755,z66,z6]),(0,[z0,z1,z2,z304,z5,z67]),(0,[z0,z1,z2,z3,z5,z756])],[(0,[z0,z1,z2,z3,z5,z757]),(0,[z91,z0,z2,z3,z5,z58]),(0,[z0,z1,z758,z3,z5,z6])],[]],
   [[(0,[z1,z2,z265,z3,z5,z98]),(0,[z0,z1,z2,z3,z5,z759]),(0,[z0,z1,z2,z760,z5,z6]),(0,[z233,z1,z2,z3,z5,z391])],[(0,[z0,z1,z2,z3,z5,z374]),(0,[z0,z761,z2,z3,z5,z6]),(0,[z0,z9,z2,z3,z5,z114]),(0,[z0,z1,z2,z3,z762,z6]),(0,[z0,z763,z2,z3,z5,z6])],[(0,[z0,z1,z53,z727,z5,z6]),(0,[z0,z764,z2,z3,z5,z6]),(0,[z128,z0,z1,z2,z5,z27])],[(0,[z19,z1,z265,z3,z5,z30]),(0,[z0,z765,z2,z3,z5,z6])],[(0,[z0,z1,z2,z162,z5,z30]),(0,[z0,z1,z2,z3,z5,z766]),(0,[z0,z1,z2,z33,z5,z6]),(0,[z0,z1,z2,z3,z5,z404])],[(0,[z0,z1,z767,z3,z5,z6]),(0,[z230,z1,z2,z3,z5,z768])],[],[(0,[z0,z1,z2,z33,z31,z6]),(0,[z243,z1,z35,z2,z3,z5]),(0,[z0,z1,z2,z769,z5,z6]),(0,[z0,z1,z2,z13,z5,z14])],[(0,[z121,z348,z265,z3,z5,z6]),(0,[z0,z1,z367,z2,z5,z30]),(0,[z180,z1,z2,z3,z5,z30]),(0,[z0,z1,z211,z2,z5,z6]),(0,[z0,z1,z2,z13,z5,z695])],[(0,[z0,z1,z770,z2,z5,z6]),(0,[z0,z1,z2,z3,z771,z67])],[(0,[z0,z1,z2,z3,z772,z6])],[(0,[z23,z1,z49,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z773]),(0,[z0,z1,z2,z5,z198,z384]),(0,[z0,z1,z3,z5,z222,z718]),(0,[z0,z1,z2,z270,z76,z77])],[(0,[z0,z1,z2,z430,z148,z6]),(0,[z254,z1,z2,z133,z5,z6])],[(0,[z0,z193,z2,z3,z5,z30]),(0,[z0,z2,z54,z3,z5,z114])],[(0,[z0,z1,z2,z3,z5,z774]),(0,[z0,z1,z49,z3,z5,z67]),(0,[z151,z1,z2,z3,z5,z67]),(0,[z8,z0,z54,z3,z5,z103]),(0,[z0,z1,z137,z3,z65,z423])],[(0,[z0,z775,z54,z3,z5,z6]),(0,[z128,z0,z1,z2,z217,z5])]],
   [[(0,[z16,z1,z2,z3,z5,z776]),(0,[z0,z1,z2,z727,z5,z6])],[(0,[z0,z1,z2,z3,z5,z777]),(0,[z0,z1,z2,z294,z5,z6]),(0,[z0,z1,z2,z750,z5,z6])],[(0,[z0,z1,z2,z3,z5,z778]),(0,[z1,z2,z779,z48,z5,z6]),(0,[z0,z1,z2,z3,z5,z780]),(0,[z0,z1,z2,z127,z182,z6])],[(0,[z654,z17,z2,z3,z5,z6])],[(0,[z19,z193,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z781]),(0,[z149,z1,z2,z48,z5,z30]),(0,[z1,z2,z3,z24,z5,z30]),(0,[z23,z1,z2,z3,z5,z67]),(0,[z0,z88,z2,z3,z5,z6])],[(0,[z17,z2,z3,z5,z553,z6]),(0,[z471,z1,z265,z3,z5,z6]),(0,[z0,z248,z2,z3,z5,z22]),(0,[z0,z1,z241,z3,z219,z6]),(0,[z0,z1,z2,z782,z5,z6])],[(0,[z783,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z740,z5,z6]),(0,[z0,z1,z598,z3,z31,z6]),(0,[z0,z1,z2,z304,z65,z6]),(0,[z128,z0,z88,z2,z3,z5])],[(0,[z784,z1,z2,z3,z5,z6]),(0,[z785,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z683,z5,z30]),(0,[z0,z1,z2,z68,z3,z26])],[(0,[z0,z106,z2,z3,z5,z6]),(0,[z0,z1,z2,z786,z3,z6]),(0,[z0,z1,z2,z787,z5,z6]),(0,[z1,z2,z3,z201,z5,z67]),(0,[z1,z788,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z26,z789])],[(0,[z0,z1,z2,z5,z6,z790])],[(0,[z156,z0,z2,z705,z5,z6]),(0,[z1,z2,z3,z5,z30,z321])],[(0,[z0,z791,z2,z3,z5,z6]),(0,[z792,z1,z2,z54,z3,z5])],[(0,[z0,z1,z2,z793,z3,z5])],[(0,[z0,z794,z2,z3,z5,z6]),(0,[z0,z1,z57,z443,z5,z6]),(0,[z0,z1,z2,z795,z5,z6]),(0,[z0,z1,z2,z3,z5,z796])],[(0,[z0,z1,z2,z797,z3,z6])]],
   [[(0,[z0,z1,z265,z3,z18,z6]),(0,[z280,z1,z2,z3,z5,z30]),(0,[z798,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z112,z5,z30]),(0,[z799,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z164,z6])],[(0,[z176,z17,z2,z3,z5,z6]),(0,[z0,z1,z2,z430,z18,z6]),(0,[z0,z1,z2,z800,z5,z67]),(0,[z0,z1,z2,z3,z5,z801])],[(0,[z0,z85,z458,z3,z5,z6]),(0,[z0,z1,z2,z3,z802,z67])],[(0,[z0,z803,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z755,z6])],[(0,[z1,z2,z3,z5,z547,z30]),(0,[z0,z348,z2,z3,z5,z67]),(0,[z322,z0,z1,z2,z5,z532]),(0,[z0,z159,z2,z3,z5,z6]),(0,[z0,z1,z136,z253,z5,z6])],[(0,[z395,z0,z88,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z804])],[(0,[z0,z1,z2,z805,z5,z30]),(0,[z8,z0,z427,z54,z3,z5]),(0,[z0,z1,z2,z609,z79,z6])],[(0,[z0,z1,z2,z3,z5,z806]),(0,[z172,z1,z265,z3,z5,z30]),(0,[z381,z1,z2,z3,z5,z807]),(0,[z0,z1,z2,z3,z808,z6])],[(0,[z1,z17,z2,z3,z5,z70]),(0,[z0,z1,z2,z5,z144,z67])],[(0,[z809,z1,z2,z3,z5,z6])],[(0,[z16,z1,z2,z3,z5,z73]),(0,[z0,z1,z2,z779,z5,z6]),(0,[z172,z0,z1,z3,z5,z43]),(0,[z0,z1,z2,z623,z3,z26])],[(0,[z0,z1,z2,z3,z5,z810]),(0,[z811,z0,z2,z3,z5,z6]),(0,[z812,z1,z2,z3,z5,z6]),(0,[z42,z0,z1,z3,z5,z718])],[(0,[z121,z1,z265,z3,z5,z116]),(0,[z254,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z573,z67]),(0,[z0,z1,z647,z3,z31,z6]),(0,[z0,z1,z2,z3,z789,z76])],[(0,[z0,z1,z2,z813,z5,z6]),(0,[z292,z0,z1,z53,z5,z6]),(0,[z0,z1,z345,z3,z5,z222]),(0,[z0,z88,z2,z3,z5,z43])],[(0,[z703,z0,z2,z3,z34,z6]),(0,[z0,z1,z216,z2,z427,z5]),(0,[z0,z1,z2,z814,z5,z6])]],
   [[(0,[z1,z2,z388,z3,z5,z30]),(0,[z187,z1,z2,z3,z5,z30]),(0,[z815,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z816,z6]),(0,[z1,z2,z3,z5,z391,z30]),(0,[z0,z1,z44,z2,z127,z30]),(0,[z0,z1,z2,z217,z5,z30]),(0,[z0,z1,z2,z3,z5,z198]),(0,[z0,z1,z2,z817,z5,z6]),(0,[z452,z1,z2,z392,z5,z6]),(0,[z818,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z382,z5,z103]),(0,[z0,z1,z2,z3,z819,z5]),(0,[z0,z1,z2,z5,z389,z6]),(0,[z0,z1,z2,z3,z5,z820])],[(0,[z21,z85,z2,z3,z66,z6]),(0,[z0,z1,z458,z237,z5,z6]),(0,[z0,z1,z2,z3,z5,z821])],[(0,[z1,z822,z2,z3,z5,z6])],[(0,[z202,z0,z216,z2,z5,z6]),(0,[z8,z0,z54,z133,z5,z6]),(0,[z0,z823,z1,z2,z3,z5]),(0,[z452,z1,z2,z217,z5,z6]),(0,[z0,z1,z824,z2,z5,z6])],[(0,[z0,z1,z2,z3,z5,z825]),(0,[z0,z1,z826,z2,z5,z6])],[(0,[z0,z1,z2,z3,z349,z155])],[(0,[z0,z1,z44,z2,z470,z6]),(0,[z0,z1,z57,z3,z5,z575]),(0,[z0,z827,z2,z3,z5,z6]),(0,[z233,z1,z2,z3,z5,z222]),(0,[z42,z0,z159,z3,z5,z43])],[(0,[z16,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z828]),(0,[z42,z0,z1,z3,z5,z321]),(0,[z0,z1,z2,z392,z5,z67]),(0,[z150,z233,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z829,z5]),(0,[z8,z254,z54,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z830])],[(0,[z0,z1,z831,z3,z5,z6]),(0,[z449,z0,z1,z2,z5,z27]),(0,[z0,z1,z2,z5,z832,z67]),(0,[z0,z168,z2,z3,z110,z6]),(0,[z0,z1,z2,z3,z833,z6])],[(0,[z0,z1,z2,z3,z5,z834]),(0,[z0,z835,z2,z3,z5,z6]),(0,[z19,z1,z836,z3,z5,z6]),(0,[z99,z1,z2,z46,z5,z6])],[(0,[z0,z1,z2,z837,z5,z6]),(0,[z121,z1,z265,z3,z5,z67]),(0,[z0,z1,z2,z3,z5,z838])],[(0,[z0,z1,z2,z3,z5,z839]),(0,[z0,z1,z2,z840,z5,z6]),(0,[z0,z1,z57,z3,z5,z6]),(0,[z69,z0,z54,z3,z5,z6]),(1,[z1,z2,z3,z841,z5])],[(0,[z0,z1,z2,z740,z5,z6]),(0,[z1,z842,z2,z3,z5,z6])]],
   [[(0,[z254,z1,z2,z3,z5,z843]),(0,[z0,z1,z2,z3,z5,z844]),(0,[z0,z1,z2,z5,z845,z6]),(0,[z846,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z573,z79,z6])],[(0,[z0,z1,z2,z354,z5,z67]),(0,[z0,z1,z450,z3,z5,z391]),(0,[z0,z1,z2,z3,z847,z6]),(0,[z0,z1,z2,z3,z848,z6])],[(0,[z0,z1,z2,z849,z5,z6]),(0,[z0,z1,z2,z430,z5,z6]),(0,[z0,z1,z2,z850,z5,z6]),(0,[z1,z2,z624,z3,z5,z30]),(0,[z851,z1,z2,z3,z5,z6]),(0,[z101,z32,z2,z119,z5,z6])],[(0,[z149,z1,z2,z147,z5,z6]),(0,[z0,z1,z2,z259,z148,z6]),(0,[z0,z1,z2,z3,z5,z852])],[(0,[z0,z1,z2,z3,z853,z5]),(0,[z0,z88,z2,z3,z5,z77])],[(0,[z151,z1,z2,z3,z5,z30]),(0,[z854,z0,z1,z2,z3,z5]),(0,[z398,z0,z1,z2,z5,z27])],[(0,[z21,z85,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z855,z6]),(0,[z0,z101,z659,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z856])],[(0,[z0,z1,z2,z3,z5,z857])],[(0,[z858,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z68,z3,z789])],[(0,[z0,z1,z2,z3,z5,z859]),(0,[z0,z85,z2,z3,z5,z6]),(0,[z0,z860,z2,z3,z5,z6]),(0,[z207,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z86,z246]),(0,[z0,z1,z2,z861,z5,z6]),(0,[z0,z862,z2,z3,z5,z6]),(0,[z0,z1,z2,z270,z5,z6])],[(0,[z0,z1,z2,z3,z5,z863]),(0,[z0,z1,z163,z3,z34,z6]),(0,[z0,z1,z2,z3,z5,z423])],[(0,[z0,z1,z2,z864,z5,z6]),(0,[z0,z865,z2,z3,z5,z6]),(0,[z1,z647,z2,z3,z5,z30]),(0,[z156,z0,z2,z78,z5,z67]),(0,[z0,z1,z2,z3,z67,z866]),(0,[z0,z1,z2,z3,z5,z867]),(0,[z1,z2,z68,z3,z90,z5])],[],[(0,[z297,z0,z2,z46,z5,z6]),(0,[z0,z1,z868,z3,z5,z6]),(0,[z207,z1,z2,z3,z5,z198])],[(0,[z0,z1,z2,z3,z5,z869]),(0,[z156,z0,z2,z403,z5,z6]),(0,[z1,z2,z3,z24,z755,z6]),(0,[z0,z1,z2,z3,z870,z6])],[(0,[z0,z871,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z872,z6])]],
   [[(0,[z1,z2,z3,z779,z5,z6]),(0,[z0,z1,z2,z13,z5,z107])],[(0,[z0,z1,z873,z2,z5,z6]),(0,[z0,z1,z2,z874,z5,z6]),(0,[z0,z1,z2,z392,z178,z6]),(0,[z0,z1,z2,z3,z164,z77])],[(0,[z452,z1,z2,z3,z5,z67]),(0,[z215,z0,z1,z53,z5,z6]),(0,[z0,z1,z44,z2,z397,z6]),(0,[z0,z1,z35,z3,z5,z718]),(0,[z0,z1,z2,z3,z789,z77])],[(0,[z544,z1,z265,z3,z5,z6]),(0,[z1,z2,z664,z3,z5,z30]),(0,[z0,z875,z2,z3,z5,z6]),(0,[z359,z1,z2,z3,z5,z67]),(0,[z0,z1,z163,z354,z5,z6])],[(0,[z17,z2,z542,z3,z5,z6]),(0,[z0,z1,z2,z3,z876,z6]),(0,[z1,z2,z3,z5,z672,z30]),(0,[z1,z32,z2,z3,z5,z25]),(0,[z0,z1,z351,z41,z5,z6]),(0,[z0,z1,z877,z2,z5,z6])],[(0,[z297,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z866]),(0,[z1,z2,z46,z147,z5,z6]),(0,[z0,z1,z2,z878,z5,z6]),(0,[z0,z1,z2,z3,z357,z6]),(0,[z0,z1,z2,z879,z5,z6]),(0,[z0,z1,z2,z217,z178,z6])],[(0,[z0,z1,z2,z3,z5,z880]),(0,[z8,z0,z54,z3,z5,z67]),(0,[z207,z1,z2,z3,z5,z741])],[(0,[z0,z1,z2,z41,z5,z63]),(0,[z0,z1,z2,z3,z5,z881])],[(0,[z0,z348,z2,z3,z5,z116]),(0,[z0,z1,z2,z882,z5,z6]),(0,[z190,z1,z2,z443,z5,z6]),(0,[z215,z0,z1,z53,z82,z6])],[(0,[z0,z1,z2,z259,z18,z6]),(0,[z1,z2,z3,z5,z30,z337]),(0,[z0,z1,z2,z68,z3,z244])],[(0,[z544,z0,z54,z3,z5,z6])],[(0,[z0,z1,z44,z2,z141,z6]),(0,[z0,z1,z2,z883,z5,z6])],[(0,[z0,z1,z2,z884,z5,z6]),(0,[z0,z348,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z885]),(0,[z8,z0,z211,z54,z5,z6]),(0,[z0,z1,z2,z3,z5,z886]),(0,[z0,z1,z2,z3,z5,z887])],[(0,[z0,z1,z2,z536,z5,z67]),(0,[z0,z348,z2,z3,z5,z652]),(0,[z0,z1,z2,z133,z5,z114]),(0,[z0,z1,z2,z3,z789,z5])],[(0,[z16,z1,z2,z3,z5,z64])],[(0,[z0,z1,z2,z888,z5,z6])]],
   [[(0,[z0,z1,z2,z5,z144,z30])],[(0,[z0,z1,z2,z147,z5,z30])],[(0,[z0,z106,z2,z3,z5,z100]),(0,[z0,z248,z49,z3,z5,z6]),(0,[z1,z2,z698,z3,z5,z30]),(0,[z0,z1,z2,z889,z5,z6]),(1,[z0,z1,z3,z5,z718])],[(0,[z577,z17,z2,z3,z5,z6]),(0,[z0,z1,z890,z3,z5,z6]),(0,[z0,z85,z2,z162,z5,z6]),(0,[z1,z2,z3,z5,z30,z360]),(0,[z0,z891,z2,z3,z5,z6])],[(0,[z0,z1,z2,z892,z5,z6]),(0,[z0,z1,z2,z3,z573,z30]),(0,[z8,z230,z54,z3,z5,z6])],[(0,[z0,z193,z2,z430,z5,z6]),(0,[z0,z1,z2,z3,z5,z893]),(0,[z359,z1,z163,z3,z5,z6])],[(0,[z17,z2,z3,z5,z34,z30]),(0,[z0,z1,z894,z3,z5,z6]),(0,[z0,z1,z2,z895,z5,z6]),(0,[z207,z1,z2,z3,z5,z863]),(0,[z359,z1,z2,z3,z5,z896])],[(0,[z0,z1,z2,z3,z897,z30]),(0,[z0,z1,z2,z3,z219,z6]),(0,[z69,z0,z2,z3,z34,z6])],[(0,[z0,z1,z2,z3,z5,z898]),(0,[z1,z2,z3,z899,z5,z6])],[(0,[z515,z0,z1,z3,z31,z6])],[(0,[z152,z17,z2,z3,z5,z67]),(0,[z1,z2,z3,z5,z67,z205]),(0,[z900,z1,z2,z3,z5,z6]),(0,[z452,z1,z2,z3,z178,z6])],[(0,[z0,z248,z2,z3,z5,z67])],[(0,[z1,z2,z3,z5,z901,z30]),(0,[z0,z1,z163,z3,z5,z67]),(0,[z902,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z903]),(0,[z0,z159,z2,z217,z5,z6])],[(0,[z288,z1,z2,z3,z5,z30]),(0,[z1,z2,z49,z3,z5,z30]),(0,[z0,z101,z2,z119,z5,z25])],[(0,[z0,z1,z904,z3,z5,z6]),(0,[z331,z17,z2,z3,z5,z6]),(0,[z0,z1,z300,z41,z5,z6]),(0,[z905,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z906])],[(0,[z0,z907,z2,z3,z5,z6]),(0,[z393,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z133,z5,z30]),(0,[z1,z2,z61,z3,z5,z30]),(0,[z0,z1,z2,z392,z5,z30]),(0,[z0,z1,z2,z3,z908,z67]),(0,[z0,z1,z2,z3,z5,z909])],[(0,[z0,z1,z2,z3,z5,z910]),(0,[z128,z0,z1,z2,z5,z532]),(0,[z42,z0,z1,z3,z5,z43])],[(0,[z0,z1,z911,z2,z5,z6]),(0,[z172,z0,z1,z3,z5,z311]),(0,[z0,z1,z2,z3,z5,z912]),(0,[z0,z1,z2,z3,z178,z67]),(0,[z190,z1,z2,z3,z5,z575]),(0,[z913,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z914,z5,z30]),(0,[z0,z1,z2,z3,z5,z915])],[(0,[z121,z1,z265,z3,z5,z30]),(0,[z0,z1,z44,z2,z5,z63])],[(0,[z0,z1,z2,z3,z5,z916]),(0,[z327,z1,z2,z3,z5,z30]),(0,[z121,z1,z265,z3,z5,z652]),(0,[z120,z1,z2,z3,z24,z6]),(0,[z0,z1,z49,z3,z66,z6]),(0,[z0,z1,z2,z3,z5,z768])],[(0,[z302,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z917]),(0,[z0,z1,z2,z3,z5,z918]),(0,[z0,z1,z2,z919,z5,z6])],[(0,[z0,z1,z2,z304,z5,z30])],[(0,[z190,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z920]),(0,[z1,z313,z2,z3,z5,z30]),(0,[z0,z1,z2,z354,z5,z30]),(0,[z1,z2,z3,z90,z5,z67])],[(0,[z0,z1,z2,z259,z5,z6]),(0,[z0,z1,z2,z3,z5,z921]),(0,[z0,z1,z450,z3,z5,z222]),(0,[z0,z1,z2,z217,z26,z5])],[(0,[z0,z1,z2,z382,z5,z67]),(0,[z0,z1,z2,z3,z922,z5]),(0,[z923,z1,z2,z3,z5,z6]),(0,[z0,z924,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z547]),(0,[z0,z1,z2,z925,z5,z6])],[(0,[z926,z1,z2,z3,z5,z6]),(0,[z1,z927,z2,z3,z5,z6])],[(0,[z233,z1,z2,z3,z5,z6]),(0,[z0,z928,z2,z3,z5,z6]),(0,[z359,z1,z2,z354,z5,z6])],[(0,[z0,z1,z2,z929,z5,z6]),(0,[z0,z1,z2,z388,z3,z26]),(0,[z0,z1,z137,z496,z65,z6]),(0,[z930,z1,z2,z3,z5,z6])],[(0,[z0,z85,z2,z3,z5,z225]),(0,[z0,z1,z2,z5,z6,z931]),(0,[z1,z2,z3,z129,z5,z30]),(0,[z0,z1,z2,z3,z5,z932]),(0,[z0,z1,z2,z3,z5,z933])]],
   [[(0,[z131,z17,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z342,z77]),(0,[z0,z1,z2,z3,z5,z934])],[(0,[z0,z1,z2,z3,z5,z935]),(0,[z0,z1,z35,z363,z3,z5])],[(0,[z17,z2,z54,z3,z5,z30]),(0,[z0,z1,z936,z3,z5,z6]),(0,[z156,z0,z2,z78,z5,z30]),(0,[z0,z1,z2,z3,z937,z6])],[(0,[z0,z1,z2,z3,z219,z103])],[(0,[z0,z1,z2,z3,z5,z938]),(0,[z0,z1,z2,z3,z5,z939]),(0,[z0,z1,z44,z2,z750,z6])],[(0,[z0,z1,z2,z3,z5,z940]),(0,[z0,z941,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z942]),(0,[z0,z1,z2,z3,z5,z943]),(0,[z0,z1,z727,z3,z5,z6])],[(0,[z21,z1,z2,z237,z66,z6]),(0,[z56,z0,z2,z3,z34,z67]),(0,[z0,z1,z2,z5,z67,z384]),(0,[z0,z1,z2,z244,z5,z389])],[(0,[z0,z283,z241,z3,z5,z6]),(0,[z0,z1,z2,z213,z5,z14])],[(0,[z0,z1,z2,z621,z79,z6]),(0,[z0,z106,z2,z3,z5,z240]),(0,[z0,z1,z49,z3,z5,z30]),(0,[z0,z1,z136,z591,z5,z6]),(0,[z0,z1,z2,z944,z5,z6]),(0,[z0,z1,z2,z3,z945,z6])],[(0,[z452,z1,z2,z3,z5,z30]),(0,[z0,z2,z740,z78,z5,z6]),(0,[z0,z1,z136,z727,z5,z6])],[(0,[z359,z1,z2,z3,z5,z30])],[(0,[z0,z1,z2,z3,z711,z67]),(0,[z946,z1,z2,z3,z5,z6]),(0,[z0,z101,z2,z5,z6,z165]),(0,[z0,z1,z2,z3,z5,z742])],[(0,[z0,z1,z2,z5,z6,z947]),(0,[z0,z1,z2,z3,z244,z77])],[(0,[z1,z32,z2,z3,z5,z6]),(0,[z8,z0,z54,z3,z5,z30]),(0,[z263,z0,z2,z3,z5,z58]),(0,[z0,z1,z137,z3,z65,z6]),(0,[z0,z1,z306,z3,z65,z6])],[(0,[z0,z1,z2,z3,z5,z948]),(0,[z949,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z950])],[(0,[z0,z1,z2,z237,z5,z225]),(0,[z0,z1,z951,z3,z5,z6])]],
   [[(0,[z254,z1,z2,z382,z5,z6]),(0,[z0,z1,z952,z3,z5,z6]),(0,[z0,z1,z137,z3,z953,z6])],[(0,[z0,z1,z2,z3,z5,z954]),(0,[z0,z1,z2,z3,z5,z807]),(0,[z0,z1,z2,z955,z5,z6])],[(0,[z207,z1,z2,z48,z5,z6])],[(0,[z19,z1,z2,z3,z5,z901])],[(0,[z0,z1,z2,z956,z5,z6]),(0,[z0,z1,z2,z3,z5,z957]),(0,[z0,z1,z2,z958,z5,z6]),(0,[z0,z1,z2,z536,z5,z30]),(0,[z0,z1,z2,z5,z30,z959]),(0,[z254,z1,z2,z3,z5,z114]),(0,[z0,z1,z960,z3,z5,z6])],[(0,[z359,z1,z2,z3,z5,z739])],[(0,[z143,z1,z2,z46,z5,z6]),(0,[z0,z1,z2,z961,z5,z6])],[(0,[z291,z1,z2,z3,z24,z6]),(0,[z0,z1,z2,z962,z5,z6])],[(0,[z0,z1,z2,z3,z5,z963]),(0,[z0,z1,z2,z3,z5,z964]),(0,[z56,z0,z163,z3,z34,z6])],[(0,[z21,z1,z2,z237,z5,z30]),(0,[z1,z2,z3,z5,z67,z30]),(0,[z0,z1,z2,z3,z5,z965]),(0,[z0,z1,z2,z3,z244,z164])],[(0,[z0,z1,z2,z3,z5,z966]),(1,[z1,z836,z3,z5,z6]),(0,[z0,z85,z2,z3,z5,z22]),(0,[z0,z88,z2,z392,z5,z6])],[],[(0,[z230,z1,z2,z3,z5,z6]),(0,[z967,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z968,z5,z6]),(0,[z0,z193,z2,z259,z5,z6]),(0,[z969,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z237,z5,z6]),(0,[z0,z1,z2,z13,z5,z692]),(0,[z970,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z971,z6])],[(0,[z0,z1,z2,z5,z804,z27])],[(0,[z0,z1,z2,z972,z5,z6]),(0,[z0,z1,z2,z973,z3,z5]),(0,[z0,z1,z2,z3,z5,z974]),(0,[z0,z88,z2,z217,z5,z6])],[(0,[z0,z1,z2,z3,z975,z6]),(0,[z0,z1,z2,z5,z976,z6]),(0,[z0,z1,z2,z3,z5,z977])]],
   [[(0,[z0,z1,z978,z2,z5,z6]),(0,[z21,z1,z458,z3,z5,z30]),(0,[z979,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z980,z5,z6]),(0,[z0,z1,z2,z3,z5,z981])],[(0,[z152,z17,z2,z3,z5,z30]),(0,[z0,z1,z2,z982,z5,z6]),(0,[z1,z2,z3,z86,z24,z30]),(0,[z983,z0,z1,z2,z3,z5]),(0,[z0,z1,z984,z2,z5,z30]),(0,[z985,z1,z2,z3,z5,z6])],[(0,[z0,z248,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z986,z30])],[(0,[z0,z1,z458,z3,z5,z6]),(0,[z987,z0,z1,z2,z3,z5]),(0,[z0,z1,z163,z3,z5,z30]),(0,[z243,z1,z2,z3,z5,z67]),(0,[z509,z1,z2,z3,z5,z67])],[(0,[z356,z1,z2,z3,z5,z30]),(1,[z0,z2,z740,z5,z6]),(0,[z359,z1,z2,z3,z5,z404]),(0,[z0,z1,z2,z3,z258,z77])],[(0,[z0,z1,z2,z3,z5,z988]),(0,[z0,z1,z2,z3,z5,z989]),(0,[z0,z1,z2,z3,z5,z990]),(0,[z393,z1,z2,z3,z5,z225]),(0,[z0,z1,z2,z68,z3,z113]),(0,[z0,z1,z2,z5,z991,z6]),(0,[z0,z992,z2,z3,z5,z6])],[(0,[z156,z17,z2,z46,z5,z6]),(0,[z0,z1,z2,z3,z5,z993]),(0,[z0,z994,z2,z3,z5,z6]),(0,[z0,z101,z2,z119,z5,z6])],[(0,[z254,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z995,z5,z30]),(0,[z0,z101,z1,z2,z5,z63]),(0,[z0,z1,z2,z392,z164,z6])],[(0,[z1,z2,z3,z113,z24,z6]),(0,[z996,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z997,z5,z6])],[(0,[z0,z1,z2,z3,z18,z6]),(0,[z579,z0,z1,z3,z31,z6]),(0,[z260,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z178,z30]),(0,[z156,z0,z2,z464,z5,z6])],[(0,[z0,z1,z2,z3,z5,z998]),(0,[z0,z1,z2,z237,z5,z22]),(0,[z1,z2,z3,z999,z5,z6])],[(0,[z99,z1,z2,z46,z5,z240]),(0,[z0,z1,z2,z33,z5,z67]),(0,[z0,z1,z136,z41,z5,z6]),(0,[z0,z1,z367,z2,z5,z423]),(0,[z0,z159,z2,z392,z5,z6]),(0,[z0,z1,z2,z217,z164,z6])],[(0,[z663,z0,z1,z53,z5,z6]),(0,[z0,z1,z2,z1000,z3,z5])],[(0,[z0,z1,z2,z1001,z5,z6]),(0,[z121,z1,z836,z3,z5,z6]),(1,[z85,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z1002,z5]),(0,[z0,z1,z2,z3,z5,z1003])],[(0,[z0,z1,z584,z3,z65,z6])],[(0,[z1,z2,z3,z90,z5,z30]),(0,[z0,z1,z211,z2,z5,z67])]],
   [[(0,[z0,z1,z2,z3,z5,z1004]),(0,[z16,z1,z2,z147,z5,z30]),(0,[z0,z1,z2,z3,z1005,z6]),(0,[z56,z0,z2,z354,z34,z6])],[(0,[z156,z0,z2,z489,z5,z6]),(0,[z0,z1,z2,z382,z5,z30]),(0,[z339,z1,z2,z3,z5,z67]),(0,[z1006,z0,z2,z3,z5,z6]),(0,[z1,z2,z3,z841,z65,z5])],[(0,[z1,z2,z3,z244,z841,z5]),(0,[z0,z1007,z2,z3,z5,z6])],[(0,[z452,z88,z2,z3,z5,z6])],[(0,[z394,z1,z2,z3,z5,z30]),(0,[z0,z1,z1008,z3,z5,z6]),(0,[z0,z1,z2,z3,z357,z103])],[(0,[z1,z2,z472,z3,z5,z30]),(0,[z0,z1,z2,z3,z1009,z6])],[(0,[z0,z193,z2,z3,z148,z6]),(0,[z0,z1,z2,z1010,z5,z30]),(0,[z1011,z1,z2,z3,z5,z6])],[(0,[z243,z1,z2,z3,z5,z499]),(0,[z0,z1,z2,z1012,z5,z6])],[(0,[z152,z17,z2,z3,z5,z374]),(0,[z0,z1,z2,z1013,z5,z6]),(0,[z21,z1,z2,z3,z5,z73]),(0,[z0,z1,z2,z294,z5,z67]),(0,[z230,z1,z2,z3,z5,z103]),(1,[z0,z1,z2,z5,z804])],[(0,[z19,z1,z272,z3,z5,z6]),(0,[z1,z49,z3,z5,z6,z30]),(0,[z8,z0,z54,z382,z5,z6])],[(0,[z1,z17,z2,z3,z5,z417]),(0,[z0,z1,z1014,z2,z5,z6]),(0,[z0,z1,z2,z1015,z5,z6]),(0,[z0,z1,z2,z3,z5,z1016]),(0,[z0,z2,z3,z5,z1017,z6]),(0,[z0,z1,z2,z1018,z5,z6]),(0,[z0,z1,z2,z1019,z5,z6]),(0,[z0,z1,z2,z496,z5,z6]),(0,[z0,z1,z2,z5,z6,z804])],[(0,[z0,z88,z2,z3,z5,z67]),(0,[z395,z1020,z1,z2,z3,z5]),(0,[z0,z1,z1021,z3,z5,z6]),(0,[z42,z1,z2,z3,z90,z5])],[(0,[z0,z1,z2,z3,z5,z1022]),(0,[z0,z1,z2,z3,z5,z1023])],[(0,[z0,z1,z458,z162,z5,z6]),(0,[z56,z0,z2,z3,z34,z30]),(0,[z8,z0,z54,z3,z5,z114]),(0,[z0,z1,z163,z3,z5,z404]),(0,[z150,z0,z2,z3,z5,z1024])],[(0,[z0,z1,z1025,z3,z5,z6]),(0,[z0,z1026,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1027])],[]],
   [[(0,[z0,z106,z2,z3,z5,z67]),(0,[z0,z1,z1028,z3,z5,z6]),(0,[z0,z1,z2,z787,z5,z67]),(0,[z0,z97,z2,z119,z5,z6]),(0,[z0,z168,z2,z3,z1017,z6])],[(0,[z233,z10,z1,z2,z3,z5])],[(0,[z207,z101,z2,z119,z5,z6])],[(0,[z0,z1,z137,z3,z266,z6]),(0,[z0,z1,z602,z41,z5,z6]),(0,[z0,z1,z2,z5,z1029,z6])],[(0,[z0,z17,z2,z536,z5,z6]),(0,[z297,z0,z2,z3,z5,z240]),(0,[z0,z1,z2,z33,z65,z6]),(0,[z452,z159,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1030,z6]),(0,[z1031,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1032]),(0,[z616,z1,z2,z3,z5,z67]),(0,[z1033,z1,z2,z3,z5,z6])],[(0,[z152,z17,z2,z3,z5,z64]),(0,[z0,z1034,z2,z3,z5,z6]),(0,[z0,z101,z2,z336,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1035]),(0,[z449,z0,z1,z2,z5,z285]),(0,[z42,z0,z88,z3,z5,z43])],[(0,[z0,z1,z2,z3,z5,z1036]),(0,[z99,z1,z2,z46,z5,z100]),(0,[z0,z1,z2,z3,z164,z67]),(0,[z0,z1,z35,z3,z234,z5])],[(0,[z0,z1037,z2,z3,z5,z6]),(0,[z475,z0,z1,z3,z31,z6]),(0,[z1038,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z90,z5,z58])],[(0,[z967,z17,z2,z3,z5,z6]),(0,[z0,z1,z1039,z3,z5,z6]),(0,[z19,z1,z2,z3,z5,z116]),(0,[z0,z1,z2,z3,z1040,z6]),(0,[z1041,z0,z1,z2,z3,z5]),(0,[z637,z0,z54,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1024])],[(0,[z0,z193,z2,z3,z18,z6]),(0,[z121,z1,z265,z430,z5,z6]),(0,[z0,z159,z2,z3,z5,z67]),(0,[z0,z1,z57,z354,z5,z6]),(0,[z0,z1,z2,z53,z5,z63])],[(0,[z295,z1,z2,z3,z5,z30])],[(0,[z0,z1,z2,z3,z76,z77])],[(0,[z0,z1,z2,z1042,z5,z6]),(0,[z19,z1,z2,z3,z5,z30]),(1,[z792,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z82,z6])]],
   [[(0,[z193,z2,z265,z3,z5,z6]),(0,[z19,z1,z20,z3,z5,z142]),(0,[z21,z1,z458,z3,z66,z6]),(0,[z395,z0,z2,z3,z5,z58])],[(0,[z0,z1043,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1044,z5,z6]),(0,[z0,z1,z1045,z2,z5,z6])],[(0,[z0,z1,z2,z3,z5,z25]),(0,[z0,z1,z2,z5,z6,z384]),(0,[z0,z88,z2,z3,z178,z6]),(0,[z0,z1,z2,z13,z217,z5])],[(0,[z0,z1,z2,z3,z5,z142]),(0,[z0,z1,z2,z3,z5,z1046]),(0,[z42,z243,z1,z2,z3,z5])],[(0,[z0,z1,z1047,z3,z5,z6]),(0,[z0,z1,z2,z354,z5,z404])],[(0,[z151,z1,z2,z3,z5,z547]),(0,[z0,z1,z2,z3,z148,z6]),(0,[z0,z1,z2,z3,z5,z1048]),(0,[z0,z1,z2,z3,z5,z1049])],[],[(0,[z0,z1,z2,z746,z5,z30]),(0,[z410,z1,z2,z3,z5,z30]),(0,[z132,z0,z1,z3,z5,z321]),(0,[z0,z1,z2,z310,z79,z6]),(0,[z1050,z0,z1,z2,z3,z5])],[(0,[z149,z106,z2,z3,z5,z6]),(0,[z0,z1,z458,z3,z5,z225]),(0,[z0,z1,z2,z5,z389,z67]),(0,[z0,z1,z1051,z2,z5,z6]),(0,[z1,z2,z3,z90,z349,z5])],[(0,[z0,z1,z2,z3,z5,z1052]),(0,[z56,z190,z2,z3,z34,z6]),(0,[z1,z2,z3,z90,z5,z11]),(0,[z0,z1,z2,z3,z244,z5]),(0,[z233,z1,z2,z3,z5,z43])],[(0,[z0,z1,z2,z133,z357,z6]),(0,[z0,z1,z2,z3,z1053,z5]),(0,[z0,z1,z2,z379,z3,z26])],[(0,[z0,z1,z2,z1054,z5,z6]),(0,[z0,z1,z2,z1055,z5,z6]),(0,[z1,z2,z400,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z1056]),(0,[z0,z1,z2,z3,z5,z1057])],[(0,[z0,z1,z2,z3,z5,z1058]),(0,[z1,z2,z3,z90,z5,z14])],[(0,[z1,z2,z3,z349,z5,z30]),(0,[z359,z1,z57,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z139])],[(0,[z0,z761,z2,z3,z5,z30]),(0,[z230,z1,z2,z133,z5,z6]),(0,[z0,z1,z2,z3,z1059,z6]),(0,[z395,z0,z1,z211,z2,z5]),(0,[z156,z0,z2,z412,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z1060]),(0,[z1,z556,z2,z3,z5,z30])],[(0,[z0,z1061,z2,z3,z5,z6]),(0,[z1062,z0,z1,z2,z3,z5]),(0,[z297,z0,z2,z3,z5,z100]),(0,[z0,z1,z2,z3,z1063,z6]),(0,[z0,z1,z2,z382,z5,z114]),(0,[z0,z1,z2,z3,z5,z718])],[(0,[z0,z168,z2,z3,z110,z67]),(0,[z0,z1,z2,z1064,z5,z6]),(0,[z1065,z1,z2,z3,z5,z6]),(0,[z0,z1,z136,z40,z41,z5])],[(0,[z99,z1,z2,z46,z5,z67]),(0,[z0,z1,z2,z3,z5,z1066])],[(0,[z0,z1,z1067,z3,z5,z6]),(0,[z1,z836,z265,z3,z5,z6]),(0,[z1,z2,z3,z5,z30,z631]),(0,[z0,z159,z2,z3,z178,z6])],[(0,[z0,z1,z57,z3,z5,z67]),(0,[z1068,z1,z2,z3,z5,z6])],[(0,[z120,z1,z2,z3,z24,z242]),(0,[z0,z1,z211,z2,z5,z30]),(0,[z0,z1,z2,z5,z198,z27]),(0,[z0,z1,z2,z443,z5,z575]),(0,[z0,z1069,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z98]),(0,[z0,z85,z49,z3,z5,z6]),(0,[z0,z1,z2,z3,z1070,z6])],[(0,[z0,z1071,z2,z3,z5,z6]),(0,[z0,z1,z2,z1072,z5,z6]),(0,[z1073,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1074]),(0,[z0,z1,z2,z1075,z5,z6])],[(0,[z17,z2,z463,z3,z5,z6]),(0,[z0,z1,z2,z430,z5,z67])],[(0,[z0,z1,z2,z3,z1076,z6]),(0,[z0,z1,z2,z3,z5,z1077]),(0,[z0,z1,z2,z1078,z5,z6])],[(0,[z0,z1,z2,z3,z1079,z6])],[(0,[z0,z193,z2,z3,z5,z6]),(0,[z0,z1,z2,z443,z5,z6]),(0,[z0,z1,z2,z1080,z5,z6])],[(0,[z23,z85,z2,z3,z5,z6]),(0,[z0,z1,z2,z1081,z5,z6]),(0,[z0,z1,z2,z133,z219,z6]),(0,[z0,z1,z2,z3,z1082,z5]),(0,[z0,z1083,z2,z3,z5,z6])],[(0,[z21,z1,z2,z3,z5,z1084]),(0,[z0,z1,z137,z3,z244,z65])],[(0,[z0,z1,z2,z294,z5,z30]),(0,[z0,z1,z2,z388,z3,z419]),(0,[z0,z1,z2,z3,z5,z1085]),(0,[z207,z1,z2,z3,z5,z25]),(0,[z0,z1,z2,z41,z573,z6])]],
   [[(0,[z0,z1,z2,z3,z1086,z6]),(0,[z0,z85,z2,z3,z5,z67]),(0,[z0,z1,z2,z270,z5,z67]),(0,[z0,z2,z775,z3,z5,z6]),(0,[z1,z32,z2,z3,z5,z1087]),(0,[z233,z1,z2,z3,z5,z77])],[(0,[z0,z1,z2,z1088,z5,z6]),(0,[z0,z1,z1089,z2,z5,z6]),(0,[z0,z1,z2,z3,z1090,z5]),(0,[z0,z1,z2,z3,z31,z63])],[(0,[z0,z1,z2,z147,z5,z547]),(0,[z557,z1,z2,z46,z5,z6]),(0,[z0,z88,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z1091])],[(0,[z85,z2,z3,z5,z6,z30]),(0,[z0,z1,z2,z1092,z5,z6]),(0,[z0,z1,z2,z5,z30,z931]),(0,[z0,z1,z2,z3,z5,z1093]),(0,[z1,z2,z3,z1094,z5,z6])],[(0,[z0,z1,z2,z1095,z3,z6]),(0,[z460,z1,z2,z46,z5,z6]),(0,[z0,z1,z458,z3,z5,z22]),(0,[z0,z1096,z2,z3,z5,z6]),(0,[z0,z1097,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1098])],[(0,[z1,z17,z2,z3,z5,z73]),(0,[z429,z0,z2,z78,z5,z6]),(0,[z243,z1,z2,z3,z5,z58])],[(0,[z108,z17,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1099]),(0,[z0,z1100,z2,z3,z5,z6]),(0,[z21,z1,z2,z3,z66,z6]),(0,[z0,z1,z226,z3,z65,z6]),(0,[z0,z1,z2,z1101,z5,z6]),(0,[z0,z1,z2,z1102,z5,z6])],[(0,[z0,z348,z2,z430,z5,z6]),(0,[z0,z106,z2,z3,z5,z30]),(0,[z0,z1,z49,z237,z5,z6]),(0,[z42,z0,z1,z392,z5,z43])],[(0,[z0,z1,z2,z3,z5,z1103]),(0,[z0,z1,z367,z2,z244,z5]),(0,[z0,z1,z2,z62,z79,z6])],[(0,[z215,z0,z1,z53,z5,z67]),(0,[z0,z2,z59,z3,z5,z58])],[],[(0,[z0,z1,z1104,z3,z5,z6]),(0,[z0,z1,z2,z3,z841,z5]),(0,[z42,z0,z1,z217,z5,z43])],[(0,[z297,z0,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z357,z67]),(0,[z0,z1,z216,z2,z5,z6]),(0,[z0,z101,z1,z2,z573,z6]),(0,[z0,z1105,z1,z2,z3,z5]),(0,[z0,z1,z208,z2,z127,z6])],[(0,[z1,z2,z46,z779,z5,z6]),(0,[z0,z1,z2,z573,z389,z6])],[(0,[z0,z1,z2,z3,z5,z1106]),(0,[z0,z1,z2,z5,z77,z384]),(0,[z0,z1,z2,z62,z334,z6]),(0,[z0,z1,z2,z3,z750,z6])],[(0,[z1,z2,z265,z3,z5,z116]),(0,[z0,z1,z2,z3,z5,z225]),(0,[z0,z1,z2,z3,z164,z30]),(0,[z1107,z1,z2,z3,z5,z6]),(0,[z1108,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z1109,z6]),(0,[z0,z1,z2,z3,z1110,z5])],[],[(0,[z120,z1,z2,z3,z24,z73]),(0,[z1,z2,z3,z5,z30,z45]),(0,[z0,z1,z2,z3,z5,z1111]),(0,[z128,z233,z1,z2,z3,z5])],[(0,[z1,z17,z2,z3,z5,z30]),(0,[z121,z1,z265,z259,z5,z6]),(0,[z1,z2,z265,z3,z5,z30]),(0,[z0,z159,z2,z3,z5,z30]),(0,[z0,z1,z2,z884,z5,z67]),(0,[z233,z1,z2,z392,z5,z6]),(0,[z452,z1,z2,z3,z164,z6])],[(0,[z0,z1,z2,z1112,z5,z6]),(0,[z21,z1,z2,z3,z66,z22]),(0,[z359,z168,z2,z3,z5,z6]),(0,[z0,z1,z2,z1113,z3,z5]),(0,[z0,z681,z2,z3,z5,z11])],[(0,[z0,z1,z2,z3,z1114,z6]),(0,[z243,z1,z2,z3,z5,z11])],[(0,[z0,z1,z2,z805,z5,z6]),(0,[z0,z1,z54,z3,z219,z6]),(0,[z190,z1,z2,z354,z5,z6]),(0,[z0,z1,z2,z3,z5,z575])],[(0,[z172,z1,z265,z3,z5,z6]),(0,[z1,z2,z3,z5,z511,z30]),(0,[z0,z1,z2,z3,z5,z1115]),(0,[z233,z1,z2,z217,z5,z6])],[(0,[z19,z1,z20,z3,z5,z6]),(0,[z0,z1,z2,z3,z1116,z6])],[(0,[z1,z265,z3,z5,z309,z30]),(0,[z21,z1,z2,z3,z5,z30])],[(0,[z1,z651,z2,z3,z5,z30]),(0,[z8,z0,z54,z3,z219,z6]),(0,[z150,z0,z88,z2,z3,z5])],[(0,[z0,z1,z2,z1117,z5,z6]),(0,[z50,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1118])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z19,z1,z20,z3,z5,z70]),(0,[z0,z1,z44,z2,z573,z6])],[(0,[z1,z2,z3,z5,z807,z30]),(0,[z8,z0,z216,z54,z5,z6]),(1,[z0,z1,z3,z953,z6]),(0,[z0,z1,z2,z62,z79,z139])],[(0,[z0,z1,z2,z3,z219,z67]),(0,[z42,z0,z1,z59,z3,z5]),(0,[z0,z1,z2,z3,z5,z1119]),(0,[z60,z0,z1,z3,z31,z6]),(0,[z128,z0,z1,z2,z5,z804])],[(0,[z0,z1,z2,z3,z5,z1120]),(0,[z215,z0,z1,z53,z573,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z70]),(0,[z21,z1,z2,z162,z66,z6]),(0,[z0,z1,z2,z5,z389,z30]),(0,[z0,z1,z2,z1121,z5,z6])],[(0,[z0,z1,z2,z1122,z5,z6]),(0,[z56,z0,z57,z3,z34,z6])],[(0,[z0,z17,z2,z33,z5,z6]),(0,[z254,z1,z2,z3,z357,z6]),(0,[z1123,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z1124,z6]),(0,[z1,z1125,z2,z3,z5,z6])],[(0,[z21,z1,z2,z3,z24,z30]),(0,[z0,z2,z3,z1017,z34,z6])],[(0,[z1,z678,z2,z3,z5,z30]),(0,[z156,z0,z1,z2,z5,z63]),(0,[z0,z1,z2,z3,z573,z881])],[],[(0,[z0,z1,z2,z3,z1126,z5]),(0,[z393,z1,z2,z3,z5,z67]),(0,[z156,z32,z2,z3,z5,z6]),(0,[z0,z1,z1127,z2,z5,z6]),(0,[z1128,z1,z2,z3,z5,z6])],[(0,[z1,z682,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z1129])],[(0,[z0,z1,z2,z3,z5,z1130]),(0,[z0,z1,z2,z1131,z5,z6]),(0,[z0,z1,z2,z5,z6,z1132])],[(0,[z0,z1,z2,z162,z5,z225]),(0,[z0,z168,z2,z3,z110,z30]),(0,[z254,z1,z2,z3,z5,z885])],[(0,[z0,z1,z2,z1133,z5,z6]),(0,[z99,z1,z2,z46,z5,z30]),(0,[z0,z1,z2,z3,z5,z22]),(0,[z56,z0,z2,z3,z34,z404]),(0,[z56,z0,z2,z33,z34,z6]),(0,[z0,z1,z137,z304,z65,z6])],[],[(0,[z0,z1,z2,z430,z5,z116]),(0,[z120,z1,z2,z3,z24,z67]),(0,[z0,z1,z2,z3,z5,z1134]),(0,[z0,z1,z57,z3,z5,z30])],[(0,[z243,z1,z2,z3,z5,z30]),(0,[z0,z101,z2,z617,z5,z6]),(0,[z0,z9,z408,z3,z5,z6]),(0,[z1135,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z62,z79,z63])],[(0,[z0,z1,z2,z387,z5,z14])],[(0,[z568,z17,z2,z3,z5,z6]),(0,[z23,z1,z2,z3,z5,z547]),(0,[z190,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z1136,z5,z6]),(0,[z0,z1,z2,z1137,z3,z5]),(0,[z448,z0,z2,z78,z5,z6])]],
   [[(0,[z0,z1,z2,z430,z5,z30]),(0,[z0,z1,z2,z259,z5,z67]),(0,[z207,z1,z2,z46,z5,z6]),(0,[z1,z549,z2,z3,z5,z30]),(0,[z0,z1,z3,z65,z953,z6])],[(0,[z0,z1,z2,z430,z5,z652]),(0,[z0,z2,z119,z740,z5,z6])],[(0,[z0,z1,z2,z1138,z3,z6])],[(0,[z21,z1,z2,z162,z5,z30]),(0,[z0,z1,z2,z3,z5,z1139]),(0,[z0,z1,z2,z3,z1140,z6])],[(0,[z1,z2,z3,z559,z5,z30]),(0,[z233,z1,z2,z3,z5,z67]),(0,[z562,z1,z2,z3,z5,z67]),(0,[z254,z1,z2,z3,z219,z6]),(0,[z0,z1,z2,z3,z1141,z5]),(0,[z0,z1,z2,z3,z5,z1142])],[(0,[z0,z1,z2,z1143,z5,z6]),(0,[z0,z1,z2,z33,z5,z30])],[(0,[z16,z1,z2,z536,z5,z30]),(0,[z0,z1,z2,z162,z5,z6]),(0,[z1144,z1,z2,z3,z5,z6]),(0,[z0,z1,z1145,z3,z5,z6])],[(0,[z1,z2,z3,z5,z776,z30]),(0,[z0,z85,z2,z3,z5,z30]),(0,[z94,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z270,z5,z30]),(0,[z56,z0,z2,z294,z34,z6]),(0,[z128,z0,z1,z2,z5,z384])],[(0,[z207,z1,z2,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z64]),(0,[z0,z1,z2,z3,z5,z103])],[(0,[z0,z1,z2,z3,z5,z1146]),(0,[z669,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z5,z6,z707]),(0,[z0,z1,z2,z3,z5,z1147]),(0,[z0,z88,z2,z3,z164,z6])],[(0,[z655,z1,z20,z3,z5,z6]),(0,[z0,z1,z2,z3,z1148,z6]),(0,[z0,z1,z367,z2,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1149]),(0,[z1150,z1,z2,z3,z5,z6]),(0,[z552,z0,z2,z3,z5,z58])],[(0,[z0,z1,z2,z3,z5,z1151]),(0,[z21,z1,z2,z3,z66,z225]),(0,[z0,z1,z2,z1152,z3,z5])],[(0,[z297,z99,z2,z46,z5,z6])],[(0,[z17,z2,z119,z3,z5,z30]),(0,[z0,z348,z2,z259,z5,z6]),(0,[z149,z1,z2,z779,z5,z6]),(0,[z0,z1,z2,z382,z219,z6]),(0,[z50,z0,z1,z136,z41,z5])],[(0,[z146,z17,z2,z3,z5,z6]),(0,[z0,z1,z2,z1153,z5,z6])]],
   [[(0,[z215,z0,z1,z53,z5,z30]),(0,[z42,z0,z1,z3,z178,z43])],[(0,[z0,z1,z2,z3,z5,z1154]),(0,[z190,z1,z163,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z63])],[(0,[z202,z0,z2,z536,z5,z6]),(0,[z1,z2,z3,z5,z67,z690])],[(0,[z121,z1,z265,z3,z18,z6]),(0,[z297,z0,z2,z3,z5,z30]),(0,[z0,z1,z2,z878,z5,z30])],[(0,[z0,z1,z2,z162,z5,z22]),(0,[z655,z1,z2,z3,z5,z30]),(0,[z1,z32,z2,z3,z5,z67]),(0,[z0,z1,z137,z3,z65,z67]),(0,[z0,z1,z2,z5,z1155,z6])],[(0,[z47,z1,z2,z3,z5,z30]),(0,[z23,z1,z2,z3,z5,z142]),(0,[z23,z1,z2,z3,z5,z807]),(0,[z0,z1,z1156,z2,z5,z6])],[(0,[z149,z1,z2,z48,z5,z6]),(0,[z0,z1,z57,z3,z5,z404]),(0,[z0,z2,z3,z5,z6,z1024])],[(0,[z0,z1,z2,z3,z5,z1157]),(0,[z1158,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z1159,z5,z6]),(0,[z0,z1,z2,z5,z1160,z6])],[],[],[(0,[z106,z2,z46,z3,z5,z6]),(0,[z0,z1,z2,z1161,z3,z5]),(0,[z0,z88,z2,z3,z26,z5]),(0,[z0,z159,z2,z3,z164,z6])],[(0,[z0,z1,z2,z3,z1162,z5]),(0,[z221,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z1163]),(0,[z8,z0,z54,z3,z357,z6]),(0,[z1164,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z13,z441,z5])],[(0,[z0,z1,z2,z3,z5,z1165]),(0,[z1,z2,z836,z3,z5,z6]),(0,[z0,z1,z2,z3,z1166,z5]),(0,[z0,z1,z1167,z3,z5,z6])],[(0,[z0,z1,z2,z1168,z5,z6])],[(0,[z156,z0,z2,z704,z5,z6]),(0,[z0,z1,z2,z62,z324,z6])],[(0,[z517,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z76,z155]),(0,[z1,z32,z2,z3,z5,z1169]),(0,[z56,z359,z2,z3,z34,z6]),(0,[z0,z1,z2,z3,z1170,z6])]],
   [[(0,[z0,z1171,z2,z3,z5,z6]),(0,[z120,z1,z2,z3,z755,z6]),(0,[z1,z2,z3,z5,z67,z807])],[],[(0,[z0,z1,z2,z750,z79,z6])],[(0,[z0,z1,z2,z1172,z5,z6]),(0,[z0,z1,z2,z237,z5,z67]),(0,[z21,z1,z2,z3,z755,z6]),(0,[z230,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z112,z5,z6])],[(0,[z0,z1,z2,z3,z5,z29]),(0,[z0,z1,z137,z3,z323,z6]),(0,[z0,z1,z2,z127,z750,z6])],[(0,[z0,z1,z2,z3,z219,z30]),(0,[z1173,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1174,z5,z6])],[(0,[z0,z1,z2,z3,z897,z6])],[(0,[z16,z17,z2,z3,z5,z30]),(0,[z0,z1,z2,z5,z30,z384]),(0,[z1175,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1024,z58]),(0,[z0,z1,z3,z5,z953,z6]),(0,[z1176,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1177,z5,z6]),(0,[z0,z348,z2,z3,z148,z6]),(0,[z1178,z1,z2,z3,z5,z6])],[(0,[z99,z106,z2,z46,z5,z6]),(0,[z0,z1,z2,z3,z609,z77])],[(0,[z1,z2,z3,z641,z5,z30]),(0,[z0,z1179,z2,z3,z5,z6]),(0,[z0,z1,z458,z3,z5,z67]),(0,[z1,z2,z3,z5,z6,z807]),(0,[z186,z1,z2,z3,z5,z30])],[(0,[z1180,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1181])],[(0,[z0,z735,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1182]),(0,[z0,z1,z2,z3,z5,z1183])],[(0,[z0,z1184,z2,z3,z5,z6]),(0,[z393,z1,z2,z3,z5,z30]),(0,[z0,z101,z2,z119,z5,z67]),(0,[z0,z1,z2,z5,z6,z1185]),(0,[z50,z0,z1,z2,z5,z27])],[(0,[z0,z1,z2,z3,z5,z1186]),(0,[z0,z1,z2,z3,z5,z1187]),(0,[z1188,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1189,z5,z6]),(0,[z0,z1,z2,z1190,z5,z6])],[(0,[z0,z1,z2,z133,z5,z6]),(0,[z0,z1,z2,z427,z3,z5]),(0,[z1191,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z18,z67]),(0,[z0,z1,z2,z3,z5,z1192])],[(0,[z0,z1,z2,z3,z5,z1193]),(0,[z1194,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z789])],[(0,[z0,z1,z136,z41,z5,z67]),(0,[z0,z1,z137,z65,z389,z6])],[(0,[z195,z17,z2,z3,z5,z6]),(0,[z0,z1,z2,z259,z5,z116]),(0,[z120,z1,z2,z3,z24,z30]),(0,[z0,z1,z2,z217,z5,z6]),(0,[z0,z1,z2,z3,z5,z1195]),(0,[z0,z1,z44,z2,z127,z6])],[(0,[z0,z248,z2,z237,z5,z6])],[(0,[z0,z1,z2,z3,z5,z100]),(0,[z1,z2,z3,z5,z1196,z6])],[(0,[z7,z17,z2,z3,z5,z6]),(0,[z190,z1,z2,z3,z5,z30])],[(0,[z0,z1,z2,z259,z5,z30]),(0,[z0,z1,z836,z3,z5,z6])],[(0,[z0,z1,z2,z259,z5,z652]),(0,[z1197,z0,z2,z3,z5,z6])],[(0,[z0,z1,z775,z3,z5,z6]),(0,[z0,z1,z2,z304,z31,z6]),(0,[z0,z1,z44,z2,z504,z6]),(0,[z0,z1,z2,z3,z5,z1198])],[(0,[z0,z1,z2,z3,z1199,z6]),(0,[z50,z0,z1,z2,z217,z5])],[(0,[z1,z2,z3,z5,z499,z30]),(0,[z233,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z1200]),(0,[z0,z1,z366,z3,z65,z6])],[],[(0,[z8,z0,z775,z3,z5,z6]),(0,[z0,z1,z2,z1201,z5,z6]),(0,[z1202,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z147,z5,z98]),(0,[z0,z348,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z5,z417]),(0,[z0,z1,z2,z5,z14,z804])],[(0,[z17,z2,z3,z5,z569,z30]),(0,[z16,z1,z2,z3,z5,z70]),(0,[z0,z1,z2,z382,z357,z6]),(0,[z0,z1,z2,z3,z1203,z5])]],
   [[(0,[z121,z1,z265,z3,z148,z6]),(0,[z1,z137,z265,z3,z5,z30]),(0,[z0,z1,z216,z2,z5,z67])],[(0,[z0,z1,z2,z496,z5,z67]),(0,[z0,z1,z2,z5,z1204,z6]),(0,[z1,z35,z2,z3,z90,z5])],[(0,[z0,z1,z2,z3,z5,z1205]),(0,[z1,z2,z250,z3,z5,z30]),(0,[z0,z1,z2,z3,z771,z6]),(0,[z0,z1,z1206,z3,z5,z6])],[(0,[z231,z1,z2,z3,z5,z30]),(0,[z230,z1,z2,z382,z5,z6]),(0,[z0,z1,z2,z3,z357,z114]),(0,[z0,z10,z88,z2,z3,z5])],[(0,[z0,z1,z2,z1207,z5,z6]),(0,[z410,z1,z2,z48,z5,z6]),(0,[z21,z1,z49,z3,z5,z30]),(0,[z1,z2,z3,z5,z1084,z30]),(0,[z0,z1,z2,z3,z5,z1208]),(0,[z0,z1,z2,z53,z573,z6])],[(0,[z0,z1,z2,z3,z5,z1209]),(0,[z120,z85,z2,z3,z5,z6]),(0,[z0,z1,z2,z1210,z5,z6]),(0,[z0,z1,z2,z1211,z5,z6]),(0,[z0,z1,z1212,z2,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1213]),(0,[z150,z0,z2,z3,z5,z631]),(0,[z0,z1,z2,z130,z5,z27])],[(0,[z151,z1,z2,z3,z5,z6]),(0,[z0,z1,z49,z3,z5,z6]),(1,[z1,z2,z3,z755,z6]),(0,[z230,z1,z2,z3,z5,z114]),(0,[z190,z1,z2,z3,z5,z748]),(0,[z0,z1214,z2,z3,z5,z6])],[(0,[z0,z1,z2,z536,z5,z547]),(0,[z0,z1,z2,z1215,z5,z6]),(0,[z0,z1,z2,z3,z1017,z6]),(0,[z0,z2,z3,z110,z1017,z6]),(0,[z0,z1,z2,z1216,z5,z6])],[],[(0,[z0,z1,z2,z1217,z5,z6])],[(0,[z0,z1,z2,z3,z5,z901]),(0,[z1,z32,z2,z3,z5,z30])],[(0,[z50,z0,z1,z2,z13,z5])],[(0,[z0,z1,z2,z3,z148,z116]),(0,[z1,z2,z3,z5,z67,z212]),(0,[z0,z1,z2,z3,z5,z1218])],[(0,[z0,z1,z2,z3,z1219,z6]),(0,[z149,z1,z2,z48,z5,z29]),(0,[z1,z2,z3,z5,z1220,z6])],[(0,[z0,z1,z2,z3,z5,z1087]),(0,[z1221,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z1222,z5,z6]),(0,[z190,z1,z2,z3,z5,z404]),(0,[z0,z1,z2,z5,z702,z27])],[(0,[z0,z1,z184,z41,z5,z6]),(0,[z1,z2,z68,z3,z26,z90])],[(0,[z0,z1,z2,z3,z5,z1223]),(0,[z0,z1,z2,z3,z1224,z5])],[(0,[z452,z1,z2,z3,z5,z142])],[(0,[z0,z168,z2,z3,z284,z6]),(0,[z1225,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1226]),(0,[z1,z85,z2,z3,z5,z30]),(0,[z368,z1,z2,z3,z5,z67]),(0,[z0,z1,z2,z3,z219,z114]),(0,[z792,z1,z2,z3,z5,z6])],[(0,[z121,z193,z265,z3,z5,z6]),(0,[z0,z1,z2,z3,z357,z30]),(0,[z0,z1,z2,z3,z82,z67]),(0,[z0,z1,z35,z3,z5,z406])],[(0,[z1,z265,z3,z5,z31,z30]),(0,[z0,z1,z2,z3,z5,z1227]),(0,[z0,z1,z2,z3,z1228,z5])],[(0,[z0,z1,z2,z1229,z5,z6]),(0,[z0,z1043,z2,z3,z5,z67]),(0,[z215,z0,z1,z727,z5,z6])],[(0,[z0,z1,z2,z3,z86,z77]),(0,[z1230,z0,z1,z2,z5,z6])],[(0,[z0,z1,z2,z237,z5,z30]),(0,[z230,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z968,z5,z30])],[(0,[z0,z1,z2,z3,z5,z240]),(0,[z0,z1,z2,z800,z5,z6]),(0,[z1,z2,z3,z5,z618,z30]),(0,[z42,z0,z1,z3,z37,z5]),(0,[z0,z1,z2,z26,z5,z144]),(0,[z393,z1,z2,z68,z3,z26])],[(0,[z0,z1,z2,z3,z802,z6]),(0,[z0,z1,z2,z3,z1231,z5])],[(0,[z0,z1,z2,z3,z148,z67]),(0,[z0,z1,z2,z3,z5,z242]),(0,[z0,z1,z2,z1232,z5,z6])],[(0,[z0,z348,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z776]),(0,[z0,z1,z211,z2,z427,z5])],[(0,[z233,z1,z2,z3,z178,z6])]],
   [[(0,[z202,z0,z2,z33,z5,z6]),(0,[z0,z1,z1233,z2,z5,z6])],[(0,[z0,z1,z2,z1234,z5,z6]),(0,[z381,z1,z2,z3,z5,z30]),(0,[z1020,z1,z2,z3,z5,z6]),(0,[z32,z2,z119,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1235])],[(0,[z0,z1,z2,z3,z5,z1236]),(0,[z0,z1,z2,z5,z144,z6])],[(0,[z0,z1,z2,z147,z5,z6]),(0,[z0,z1,z2,z3,z18,z116]),(0,[z0,z1,z2,z1237,z5,z6]),(0,[z0,z1,z2,z3,z5,z843]),(0,[z0,z1,z2,z3,z5,z896]),(0,[z0,z1,z2,z5,z991,z30]),(0,[z0,z1,z2,z1055,z5,z67])],[(0,[z0,z1,z2,z3,z5,z1238]),(0,[z0,z101,z2,z119,z5,z30]),(0,[z0,z1,z2,z3,z1239,z6])],[(0,[z229,z1,z2,z3,z5,z30]),(0,[z1240,z0,z1,z2,z3,z5]),(0,[z0,z1,z1241,z3,z5,z6])],[(0,[z0,z1,z2,z1242,z5,z6]),(0,[z1,z2,z3,z113,z24,z30]),(0,[z0,z1,z2,z3,z573,z6]),(0,[z0,z1243,z2,z3,z5,z6]),(0,[z42,z0,z1,z3,z164,z43])],[(0,[z0,z1,z2,z3,z1244,z6]),(0,[z0,z1,z2,z3,z18,z30]),(0,[z0,z1,z2,z3,z5,z1245]),(0,[z0,z1246,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1247,z5])],[(0,[z0,z1,z2,z3,z5,z1248]),(0,[z0,z1,z2,z3,z18,z652]),(0,[z149,z1,z2,z48,z5,z417]),(0,[z0,z1,z2,z3,z5,z1249]),(0,[z0,z101,z2,z740,z5,z6]),(0,[z42,z0,z1,z210,z3,z5])],[(0,[z0,z1,z2,z1250,z5,z6]),(0,[z0,z1,z136,z41,z5,z30]),(0,[z1,z2,z169,z3,z5,z30])],[(0,[z0,z1,z2,z3,z5,z1251]),(1,[z0,z2,z3,z1017,z6])],[(0,[z0,z1,z2,z3,z5,z1252]),(0,[z60,z0,z1,z3,z953,z6])],[(0,[z156,z17,z2,z3,z5,z30]),(0,[z19,z1,z521,z3,z5,z6]),(0,[z0,z1,z2,z5,z67,z1253]),(0,[z0,z792,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1254,z6]),(0,[z0,z1,z2,z3,z1255,z6]),(0,[z0,z1,z2,z62,z657,z6]),(0,[z359,z1,z2,z443,z5,z6]),(0,[z0,z1,z2,z26,z5,z384]),(0,[z0,z1,z2,z3,z953,z6]),(0,[z1256,z1,z2,z3,z5,z6]),(0,[z0,z88,z2,z13,z3,z5])],[(0,[z288,z0,z1,z3,z31,z6]),(0,[z0,z1,z2,z3,z5,z1257]),(0,[z0,z1,z2,z387,z5,z84]),(0,[z0,z1,z2,z3,z635,z77])],[(0,[z967,z152,z2,z3,z5,z6]),(0,[z326,z1,z2,z3,z5,z30])],[]],
   [[(0,[z0,z1,z2,z3,z1258,z6]),(0,[z667,z1,z2,z3,z5,z30]),(1,[z0,z1,z2,z750,z6])],[(0,[z0,z1,z2,z5,z6,z1259]),(0,[z1260,z1,z2,z3,z5,z6]),(1,[z0,z1,z727,z5,z6])],[(0,[z0,z1,z2,z1261,z5,z6]),(0,[z0,z1,z2,z392,z5,z6])],[(0,[z0,z193,z2,z3,z5,z67]),(0,[z0,z1,z2,z443,z5,z67])],[(0,[z21,z1,z49,z3,z66,z6]),(0,[z0,z1,z2,z5,z832,z6]),(0,[z0,z1,z399,z3,z5,z309]),(0,[z0,z1,z2,z354,z5,z575])],[(0,[z0,z1,z2,z914,z5,z6]),(0,[z1,z2,z3,z5,z390,z30]),(0,[z0,z1,z2,z1010,z5,z6]),(0,[z0,z1,z2,z3,z5,z1262])],[(0,[z703,z1,z2,z3,z66,z6]),(0,[z121,z1,z265,z3,z5,z6]),(0,[z0,z1,z2,z1263,z5,z6]),(0,[z287,z0,z1,z3,z31,z6]),(0,[z1264,z1,z2,z3,z5,z6]),(0,[z233,z159,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1265,z5,z6])],[(0,[z1266,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z73]),(0,[z0,z1,z2,z304,z5,z6])],[(0,[z0,z1,z2,z354,z5,z6]),(0,[z215,z0,z1,z456,z5,z6])],[(0,[z1,z2,z3,z5,z225,z30]),(0,[z108,z0,z2,z3,z5,z307]),(0,[z0,z1,z2,z1267,z5,z6]),(0,[z0,z262,z2,z3,z110,z6])],[(0,[z0,z1,z163,z3,z110,z6]),(0,[z1,z2,z3,z90,z5,z27])],[(0,[z0,z1,z49,z3,z5,z225]),(0,[z21,z1,z2,z3,z66,z67]),(0,[z282,z0,z1,z3,z31,z6]),(0,[z0,z1,z2,z3,z1268,z6])],[(0,[z0,z248,z458,z3,z5,z6])],[(0,[z207,z1,z2,z147,z5,z6]),(0,[z0,z1,z2,z3,z5,z1269]),(0,[z0,z1,z2,z62,z79,z67])]],
   [[(0,[z0,z1,z2,z3,z5,z1270]),(0,[z0,z1,z2,z3,z5,z1271]),(0,[z215,z0,z1,z513,z5,z6]),(0,[z0,z1,z2,z1272,z5,z6])],[],[(0,[z0,z1273,z2,z3,z5,z6]),(0,[z0,z1,z2,z312,z5,z107]),(0,[z1,z2,z3,z1274,z5,z6])],[(0,[z0,z1,z2,z3,z5,z116]),(0,[z0,z1,z2,z3,z5,z1275]),(0,[z23,z1,z2,z3,z5,z225]),(0,[z1,z428,z2,z3,z5,z30]),(0,[z233,z1,z2,z3,z26,z5])],[(0,[z0,z1,z2,z3,z5,z1276]),(0,[z156,z0,z2,z78,z5,z6]),(0,[z1277,z0,z1,z2,z3,z5])],[(0,[z0,z1,z163,z443,z5,z6]),(0,[z637,z0,z1,z3,z5,z43]),(0,[z0,z1,z1278,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z1279])],[(0,[z1280,z0,z1,z2,z3,z5]),(0,[z0,z1281,z2,z3,z5,z6]),(0,[z99,z1,z2,z779,z5,z6]),(0,[z0,z1,z2,z3,z5,z1282]),(0,[z359,z1,z2,z3,z5,z575])],[(0,[z0,z1,z2,z3,z1283,z6]),(0,[z1284,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1285])],[(0,[z703,z1,z2,z3,z5,z30]),(0,[z0,z1286,z2,z3,z5,z6]),(0,[z0,z1287,z2,z3,z5,z6])],[(0,[z190,z1,z57,z3,z5,z6])],[(0,[z1288,z0,z1,z2,z3,z6]),(0,[z452,z1,z2,z3,z5,z6])],[(0,[z359,z1,z2,z3,z5,z6]),(0,[z16,z202,z2,z3,z5,z30]),(0,[z471,z1,z2,z3,z66,z6]),(0,[z156,z0,z1,z2,z573,z6]),(0,[z0,z1,z2,z3,z1090,z573]),(0,[z1289,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z1290,z5,z6]),(0,[z16,z1,z2,z3,z5,z417])],[(0,[z120,z1,z2,z3,z641,z6]),(0,[z21,z248,z2,z3,z66,z6]),(0,[z0,z1,z137,z3,z65,z30]),(0,[z0,z1,z2,z133,z5,z103]),(0,[z0,z1,z2,z3,z65,z63]),(0,[z0,z1,z2,z3,z26,z164])],[(0,[z0,z1291,z2,z3,z5,z6]),(0,[z19,z1,z20,z3,z5,z67]),(0,[z8,z0,z54,z3,z5,z6]),(0,[z0,z1,z2,z76,z144,z77])]],
   [[(0,[z1,z2,z3,z65,z24,z30]),(0,[z254,z9,z2,z3,z5,z6])],[(1,[z1,z2,z779,z5,z6]),(0,[z21,z1,z2,z3,z666,z6]),(0,[z467,z1,z2,z3,z5,z30])],[(0,[z395,z0,z1,z216,z2,z5]),(0,[z1,z32,z2,z3,z5,z198]),(0,[z1,z1292,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z144,z77])],[(0,[z0,z1,z2,z3,z5,z67]),(0,[z0,z469,z2,z119,z5,z6]),(0,[z0,z1,z1293,z3,z5,z6]),(0,[z0,z1,z2,z5,z389,z423]),(0,[z0,z1,z1294,z2,z5,z6]),(0,[z42,z233,z1,z3,z5,z43])],[(0,[z1,z2,z466,z3,z5,z30]),(0,[z0,z1,z2,z1295,z3,z5]),(0,[z0,z1,z2,z3,z148,z30]),(0,[z0,z1,z49,z3,z24,z6]),(0,[z150,z0,z2,z3,z5,z58])],[(0,[z0,z1,z2,z3,z5,z1296]),(0,[z0,z1,z2,z3,z148,z652]),(0,[z60,z0,z1,z3,z31,z67]),(0,[z0,z1,z2,z62,z389,z6]),(0,[z0,z1,z3,z5,z6,z718])],[(0,[z0,z1,z2,z536,z5,z6]),(0,[z56,z0,z2,z3,z1017,z6]),(0,[z1,z2,z3,z841,z5,z6])],[(0,[z1,z2,z3,z5,z481,z30])],[(0,[z0,z1,z49,z3,z5,z22]),(0,[z1297,z1,z2,z3,z5,z6])],[(0,[z605,z1,z2,z3,z5,z67])],[(0,[z585,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z1298])],[(0,[z0,z1,z2,z3,z5,z1299]),(0,[z395,z792,z1,z2,z3,z5]),(0,[z0,z1,z2,z62,z456,z6])],[(0,[z0,z1300,z2,z3,z5,z6]),(0,[z254,z2,z54,z3,z5,z6]),(0,[z728,z1,z2,z3,z244,z5])],[(0,[z967,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1301]),(0,[z0,z1,z2,z3,z1302,z6])],[(0,[z0,z1,z2,z3,z5,z1303]),(0,[z0,z1,z2,z3,z5,z1169]),(0,[z0,z10,z2,z3,z5,z501]),(0,[z0,z1,z2,z5,z1304,z6])],[(0,[z297,z0,z2,z48,z5,z6]),(0,[z471,z1,z2,z3,z5,z30]),(0,[z0,z1,z163,z3,z5,z575]),(0,[z56,z0,z2,z443,z34,z6]),(0,[z0,z1,z2,z1305,z5,z6])]],
   [[(0,[z0,z1,z20,z3,z18,z6]),(0,[z108,z0,z2,z3,z5,z58])],[(0,[z21,z248,z2,z3,z5,z30]),(0,[z386,z0,z2,z3,z5,z631]),(0,[z1306,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z507,z5,z30])],[(0,[z152,z17,z2,z3,z5,z6]),(0,[z0,z1,z984,z2,z5,z6]),(0,[z1,z2,z3,z24,z5,z73]),(0,[z0,z1,z367,z137,z65,z6]),(0,[z1307,z1,z2,z3,z5,z6])],[(0,[z0,z248,z2,z3,z5,z6]),(0,[z0,z1,z49,z162,z5,z6]),(0,[z0,z1,z458,z3,z5,z30]),(0,[z1,z2,z3,z5,z755,z6]),(0,[z689,z0,z1,z3,z31,z6]),(0,[z0,z1,z2,z3,z986,z6]),(0,[z0,z1,z2,z1308,z5,z6]),(0,[z0,z1,z3,z953,z31,z6]),(0,[z42,z452,z1,z3,z5,z43])],[(0,[z0,z1,z163,z3,z5,z6]),(0,[z0,z1,z1309,z3,z5,z6]),(0,[z0,z1,z2,z1310,z5,z6])],[(0,[z0,z193,z2,z3,z5,z116]),(0,[z1311,z1,z2,z3,z5,z6]),(0,[z359,z2,z3,z5,z34,z6]),(0,[z0,z1,z2,z217,z5,z77])],[(0,[z0,z17,z216,z2,z5,z6]),(0,[z85,z2,z3,z5,z66,z6]),(0,[z0,z1,z2,z1312,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1313]),(0,[z233,z88,z2,z3,z5,z6])],[(0,[z254,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z908,z6]),(0,[z0,z1,z2,z995,z5,z6]),(0,[z0,z1,z2,z1138,z3,z67])],[(0,[z0,z1,z2,z443,z5,z30])],[(0,[z0,z193,z2,z3,z5,z652]),(0,[z0,z1,z2,z1314,z5,z6]),(1,[z1,z49,z3,z5,z30]),(0,[z0,z1,z2,z1315,z5,z6]),(0,[z0,z101,z2,z119,z5,z198]),(0,[z0,z1,z2,z3,z178,z6])],[(0,[z0,z1,z2,z3,z5,z64]),(0,[z0,z1,z2,z3,z1316,z6]),(0,[z19,z1,z2,z3,z5,z98]),(0,[z0,z1,z584,z53,z5,z6])],[(0,[z0,z1,z2,z1317,z5,z6]),(0,[z0,z1,z2,z3,z1318,z5]),(0,[z0,z1,z2,z3,z5,z1319]),(0,[z0,z1,z2,z162,z5,z67]),(0,[z1,z2,z3,z5,z358,z30])],[(0,[z0,z1,z2,z3,z1320,z6]),(0,[z1,z20,z836,z3,z5,z6]),(0,[z0,z1,z2,z1321,z5,z6]),(0,[z0,z1,z2,z13,z5,z303])],[(0,[z469,z1,z2,z46,z5,z6]),(0,[z168,z17,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z1084]),(0,[z207,z1,z2,z3,z5,z67]),(0,[z0,z88,z2,z3,z5,z222])]],
   [[(0,[z0,z1,z2,z3,z5,z1322]),(0,[z230,z1,z2,z3,z5,z844]),(0,[z395,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1323,z6]),(0,[z0,z1,z2,z5,z1324,z6]),(0,[z1325,z0,z1,z2,z3,z5]),(0,[z1,z2,z3,z90,z5,z6]),(0,[z0,z1,z367,z2,z5,z67]),(0,[z1326,z1,z2,z3,z5,z6])],[(0,[z0,z1097,z2,z3,z5,z30]),(0,[z0,z1,z2,z1327,z5,z6]),(0,[z1328,z0,z1,z2,z3,z5]),(0,[z1329,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z13,z5,z804])],[(0,[z0,z1,z2,z382,z5,z6]),(0,[z0,z1,z2,z5,z1330,z6])],[(0,[z108,z17,z2,z3,z5,z30]),(0,[z0,z1,z2,z536,z5,z98]),(0,[z21,z1,z2,z3,z66,z30]),(0,[z1,z2,z3,z24,z31,z30]),(1,[z1,z2,z3,z5,z807]),(0,[z0,z1,z44,z2,z378,z6])],[(0,[z233,z1,z2,z3,z164,z6]),(0,[z0,z1,z2,z3,z5,z1331])],[(0,[z9,z17,z2,z3,z5,z30]),(0,[z0,z1,z2,z1332,z3,z5]),(0,[z0,z1,z2,z62,z79,z30]),(0,[z0,z1,z2,z3,z5,z1333])],[(0,[z0,z1,z2,z3,z5,z114]),(0,[z0,z1,z2,z3,z1334,z5]),(0,[z0,z1,z2,z3,z5,z1335])],[(0,[z557,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z38,z3,z113])],[(0,[z0,z1,z2,z3,z5,z1336]),(0,[z0,z1,z2,z5,z6,z1253]),(0,[z0,z85,z2,z237,z5,z6]),(0,[z1,z2,z541,z3,z5,z30]),(0,[z56,z0,z2,z3,z34,z575]),(0,[z305,z0,z1,z53,z5,z6]),(0,[z0,z1,z2,z3,z5,z1337])],[(0,[z0,z1,z216,z2,z5,z30]),(0,[z460,z1,z2,z3,z5,z30]),(0,[z150,z243,z2,z3,z5,z58]),(0,[z0,z1,z2,z3,z1338,z6])],[(0,[z1,z2,z3,z5,z142,z30]),(0,[z0,z1,z2,z496,z5,z30]),(0,[z156,z0,z2,z36,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1339]),(0,[z629,z1,z2,z3,z5,z30]),(0,[z0,z1,z2,z3,z5,z1340])],[(0,[z0,z1,z2,z5,z6,z959]),(0,[z149,z1,z2,z48,z5,z67]),(0,[z0,z1,z2,z3,z1341,z6]),(0,[z1342,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z13,z5,z198]),(0,[z0,z1,z2,z5,z79,z63])],[(0,[z0,z248,z2,z162,z5,z6]),(0,[z220,z1,z2,z3,z5,z30]),(0,[z0,z2,z3,z5,z1343,z6])],[(0,[z0,z1,z1344,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1345]),(0,[z56,z0,z2,z3,z34,z6]),(0,[z0,z1,z2,z3,z789,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 510) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 510).take 512) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1022).take 305) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1327)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [510, 512, 305] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 166).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 166).take 153).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 319).take 160).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 479).take 33).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [166, 153, 160, 33] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_36254

theorem PEqualNP.Outside.L_meta_36254 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276681416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276681416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36254.solve