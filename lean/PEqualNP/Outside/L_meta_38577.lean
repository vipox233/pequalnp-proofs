import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38577

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
  Nat.testBit (4276677320 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0008d898c16315ca#64 ++ 0x80008d898c16315c#64 ++ 0x6019f9f9c3e73fcf#64 ++ 0x66019f9f9c3e73fc#64 : BitVec 256),
   (0x00e22a4363284c53#64 ++ 0x000e22a4363284c5#64 ++ 0xb1e63e4fe338ccfe#64 ++ 0xeb1e63e4fe338ccf#64 : BitVec 256),
   (0x2605458c0c15b0ac#64 ++ 0x02605458c0c15b0a#64 ++ 0xee07c78e3c3ff0fd#64 ++ 0xfee07c78e3c3ff0f#64 : BitVec 256),
   (0x4b7007603680ea00#64 ++ 0x04b7007603680ea0#64 ++ 0xfff807f03fc0ff0b#64 ++ 0xffff807f03fc0ff0#64 : BitVec 256),
   (0x9dbfb8003bfe0000#64 ++ 0x09dbfb8003bfe000#64 ++ 0xdffff8003fff0007#64 ++ 0xfdffff8003fff000#64 : BitVec 256),
   (0x1fdff7ff80000000#64 ++ 0x11fdff7ff8000000#64 ++ 0x1fffffffc000000f#64 ++ 0xd1fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [7, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0008980001620000 0x0000898000162000 0x4019f80003e70007 0x64019f80003e7000

def z1 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x6019f9f9c3e73fcf 0x66019f9f9c3e73fc

def z2 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1e63e4fe338ccfe 0xeb1e63e4fe338ccf

def z3 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee07c78e3c3ff0fd 0xfee07c78e3c3ff0f

def z4 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0xfffffffffc3ff0ff 0xffffffffffc3ff0f

def z5 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfff807f03fc0ff0b 0xffff807f03fc0ff0

def z6 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffff8003fff0007 0xfdffff8003fff000

def z7 : W := mkw 0x1f1dd5bc80000000 0x11f1dd5bc8000000 0x0e19c1b000000001 0x10e19c1b00000000

def z8 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1fffffffc000000f 0xd1fffffffc000000

def z9 : W := mkw 0x1fffffffe3284c53 0x11fffffffe3284c5 0xbfffffffe338ccff 0xfbfffffffe338ccf

def z10 : W := mkw 0x024047ff80000000 0x1024047ff8000000 0x000007ffc0000008 0x0000007ffc000000

def z11 : W := mkw 0x9d1d900018d60000 0x09d1d900018d6000 0x4e19c0001cc70001 0x14e19c0001cc7000

def z12 : W := mkw 0x2200458c0c15b0ac 0x02200458c0c15b0a 0xe000078e3c3ff0f8 0x2e000078e3c3ff0f

def z13 : W := mkw 0x5ffffffff7e3ffca 0x95ffffffff7e3ffc 0xffffffffffe7ffcf 0xfffffffffffe7ffc

def z14 : W := mkw 0x0938980033e20000 0x00938980033e2000 0xdff9f8003fe70007 0xfdff9f8003fe7000

def z15 : W := mkw 0x4b789f6037e2ea00 0x04b789f6037e2ea0 0xfff9fff03fe7ff0f 0xffff9fff03fe7ff0

def z16 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa00000002338ccf0 0x2a00000002338ccf

def z17 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e63e4fc000000e 0xc11e63e4fc000000

def z18 : W := mkw 0x0910000010800000 0x0091000001080000 0x4e1800001cc00001 0x14e1800001cc0000

def z19 : W := mkw 0x00e2224322084811 0x000e222432208481 0x91e606062018c030 0x891e606062018c03

def z20 : W := mkw 0x0000000000011088 0x0000000000001108 0x60000000002730c0 0x260000000002730c

def z21 : W := mkw 0x4970026032804a00 0x04970026032804a0 0x71f801f003c03f0b 0x671f801f003c03f0

def z22 : W := mkw 0x0008d09880431188 0x80008d0988043118 0x0001c00000070000 0x00001c0000007000

def z23 : W := mkw 0x9dbfb0003a9c0000 0x09dbfb0003a9c000 0x9ffff8003c180007 0xd9ffff8003c18000

def z24 : W := mkw 0x0b58d7f880000000 0x00b58d7f88000000 0x1ff9fff9c000000f 0xd1ff9fff9c000000

def z25 : W := mkw 0x3f1dd5bc8c15b0ac 0x13f1dd5bc8c15b0a 0xee1fc7be3c3ff0fd 0xfee1fc7be3c3ff0f

def z26 : W := mkw 0xdfffbf637ffeee53 0x0dfffbf637ffeee5 0xffffffffffffffff 0xffffffffffffffff

def z27 : W := mkw 0x5fdff7ff9480a200 0x15fdff7ff9480a20 0x5fffffffdcc0330f 0xd5fffffffdcc0330

def z28 : W := mkw 0x9d1dd898d9f715ca 0x89d1dd898d9f715c 0x6e19f9f9dfe73fcf 0x76e19f9f9dfe73fc

def z29 : W := mkw 0x3fffffffef3dfcff 0x13fffffffef3dfcf 0xffffffffff3ffcff 0xfffffffffff3ffcf

def z30 : W := mkw 0x624047ec0401faac 0x0624047ec0401faa 0x200007fe0000fff8 0x0200007fe0000fff

def z31 : W := mkw 0x00000800416315ca 0x800000800416315c 0x6000000003e73fc0 0x26000000003e73fc

def z32 : W := mkw 0x802008003bfe0000 0x0802008003bfe000 0xc00000003fff0000 0x2c00000003fff000

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x601801f003c03f0b 0x6601801f003c03f0

def z34 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xf1fe3fffe3f8ffff 0xef1fe3fffe3f8fff

def z35 : W := mkw 0x4970026032804a00 0x04970026032804a0 0x11f8007003c00f02 0x011f8007003c00f0

def z36 : W := mkw 0x4bf22f6377a8ee53 0x04bf22f6377a8ee5 0xfffe3ffffff8ffff 0xffffe3ffffff8fff

def z37 : W := mkw 0x9dffba437bfe4c53 0x09dffba437bfe4c5 0xfffffe4fffffccff 0xffffffe4fffffccf

def z38 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11f83871c0000002 0x011f83871c000000

def z39 : W := mkw 0x348ff09f881510ac 0x1348ff09f881510a 0x0007f80fc03f00f4 0x00007f80fc03f00f

def z40 : W := mkw 0x020005000400a000 0x0020005000400a00 0xee0007803c00f009 0xfee0007803c00f00

def z41 : W := mkw 0x1ddff2ff80000000 0x11ddff2ff8000000 0x11fff87fc0000006 0x011fff87fc000000

def z42 : W := mkw 0x00eafadbe36b5ddb 0x800eafadbe36b5dd 0xf1ffffffe3ffffff 0xef1ffffffe3fffff

def z43 : W := mkw 0x9dffba433bfe4811 0x09dffba433bfe481 0xdffffe063fffc037 0xfdffffe063fffc03

def z44 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x91e63e0fe038c0f4 0x891e63e0fe038c0f

def z45 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x0001f809c02700c4 0x00001f809c02700c

def z46 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0x9fe006003c00c000 0x99fe006003c00c00

def z47 : W := mkw 0x9db720003a9c0000 0x09db720003a9c000 0x9fe600003c180000 0x99fe600003c18000

def z48 : W := mkw 0x0405000008140000 0x0040500000814000 0xce07c0003c3f0005 0xfce07c0003c3f000

def z49 : W := mkw 0x2200458c0401b0ac 0x02200458c0401b0a 0x2000078e0000f0f8 0x02000078e0000f0f

def z50 : W := mkw 0x948fb800097e0000 0x0948fb800097e000 0x0007f800003f0004 0x00007f800003f000

def z51 : W := mkw 0x424007600400ea00 0x0424007600400ea0 0x200007f00000ff08 0x0200007f00000ff0

def z52 : W := mkw 0x0938d898f3e315ca 0x80938d898f3e315c 0xfff9f9f9ffe73fcf 0xffff9f9f9ffe73fc

def z53 : W := mkw 0x00089810c1620542 0x800089810c162054 0x00183871c3c00f02 0x000183871c3c00f0

def z54 : W := mkw 0x260505040c14a024 0x0260505040c14a02 0x8e0606063c18c030 0x98e0606063c18c03

def z55 : W := mkw 0x0082280341280453 0x0008228034128045 0x00003801c0000000 0x000003801c000000

def z56 : W := mkw 0x6f7547ec3e95faac 0x06f7547ec3e95faa 0xfff9c7f03fc7ff0b 0xffff9c7f03fc7ff0

def z57 : W := mkw 0x1dbfb00032800000 0x01dbfb0003280000 0xdffff8003fc00007 0xfdffff8003fc0000

def z58 : W := mkw 0x1d9fb00000000000 0x01d9fb0000000000 0x1ffff80000000007 0xd1ffff8000000000

def z59 : W := mkw 0xb48ff88c097f10ac 0x0b48ff88c097f10a 0x0007f80e003f00f4 0x00007f80e003f00f

def z60 : W := mkw 0x1d9ff09f80000000 0x11d9ff09f8000000 0x1ffff80fc0000007 0xd1ffff80fc000000

def z61 : W := mkw 0x1fdfffffc16315ca 0x91fdfffffc16315c 0x7fffffffc3e73fcf 0xf7fffffffc3e73fc

def z62 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x9fe7f8003c3f0004 0x99fe7f8003c3f000

def z63 : W := mkw 0x402000003680ea00 0x0402000003680ea0 0xe00000003fc0ff00 0x2e00000003fc0ff0

def z64 : W := mkw 0x0208dd98c563b5ca 0x80208dd98c563b5c 0xee19fff9ffe7ffcf 0xfee19fff9ffe7ffc

def z65 : W := mkw 0x9fbfbd003ffea000 0x09fbfbd003ffea00 0xffffff803ffff00f 0xfffffff803ffff00

def z66 : W := mkw 0x1ddfb27380000000 0x11ddfb2738000000 0x1ffff871c0000007 0xd1ffff871c000000

def z67 : W := mkw 0x00c22a4341200442 0x000c22a434120044 0x31e63e4fc3200cce 0xe31e63e4fc3200cc

def z68 : W := mkw 0x26254d8c6f3dfcff 0x026254d8c6f3dfcf 0xee07c78e3f3ffcfd 0xfee07c78e3f3ffcf

def z69 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfffe07fe3ff8ffff 0xffffe07fe3ff8fff

def z70 : W := mkw 0x99bab80033ea0000 0x099bab80033ea000 0x11f8380003c00002 0x011f8380003c0000

def z71 : W := mkw 0x4b78dff8f7e3ffca 0x84b78dff8f7e3ffc 0xfff9fff9ffe7ffcf 0xffff9fff9ffe7ffc

def z72 : W := mkw 0x2200458c0401b0ac 0x02200458c0401b0a 0xee00078e3c00f0f9 0xfee00078e3c00f0f

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0xa006060e2038c0fc 0xea006060e2038c0f

def z74 : W := mkw 0x893008003bfe0000 0x0893008003bfe000 0xdff800003fff0003 0xfdff800003fff000

def z75 : W := mkw 0xbfbffd8c3fffb0ac 0x0bfbffd8c3fffb0a 0xffffff8e3ffff0ff 0xfffffff8e3ffff0f

def z76 : W := mkw 0x0008d09880000000 0x00008d0988000000 0x0001f809c0000004 0x00001f809c000000

def z77 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x5ff9f8001fc70003 0x15ff9f8001fc7000

def z78 : W := mkw 0x99bab8003bfe0000 0x099bab8003bfe000 0xd1f838003fff0002 0x2d1f838003fff000

def z79 : W := mkw 0x0008d09880011088 0x00008d0988001108 0x6019f9f9c02730cf 0x66019f9f9c02730c

def z80 : W := mkw 0xddbfb8003ffeea00 0x0ddbfb8003ffeea0 0xfffff8003fffff07 0xffffff8003fffff0

def z81 : W := mkw 0x00089810c1620542 0x800089810c162054 0x4019f871c3e70f07 0x64019f871c3e70f0

def z82 : W := mkw 0x0000408800011088 0x0000040880001108 0x0001c008002700c4 0x00001c008002700c

def z83 : W := mkw 0x19daf2fb80000000 0x119daf2fb8000000 0x11f9f9f9c000000f 0x411f9f9f9c000000

def z84 : W := mkw 0x0b50076000000000 0x00b5007600000000 0x1ff807f00000000b 0xd1ff807f00000000

def z85 : W := mkw 0x0000408800011088 0x0000040880001108 0x6001c188002730cd 0x66001c188002730c

def z86 : W := mkw 0x1fdfb77780000000 0x11fdfb7778000000 0x1ffe3e77c0000002 0x91ffe3e77c000000

def z87 : W := mkw 0x260ddd9ccd77b5ee 0x8260ddd9ccd77b5e 0xee1fffffffffffff 0xfee1ffffffffffff

def z88 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x11e03841c3000c02 0x011e03841c3000c0

def z89 : W := mkw 0x49f22a6373a84e53 0x049f22a6373a84e5 0x11f83871c3c00f02 0x011f83871c3c00f0

def z90 : W := mkw 0x00a2280063284c53 0x000a2280063284c5 0xb1e638002338ccf6 0xeb1e638002338ccf

def z91 : W := mkw 0x0000409880011188 0x8000040988001118 0x000001b000003300 0x0000001b00000330

def z92 : W := mkw 0x148ff09f80000000 0x1148ff09f8000000 0x0007f80fc0000004 0x00007f80fc000000

def z93 : W := mkw 0x1fd7276700000000 0x11fd727670000000 0x1fe6060600000000 0x91fe606060000000

def z94 : W := mkw 0x9dbff898fbff15ca 0x89dbff898fbff15c 0xfffff9f9ffff3fcf 0xffffff9f9ffff3fc

def z95 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x6019c1b003e73fc1 0x26019c1b003e73fc

def z96 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0x4e01c1801c073001 0x14e01c1801c07300

def z97 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xce07c7863c1ff031 0x9ce07c7863c1ff03

def z98 : W := mkw 0x0000080041280453 0x0000008004128045 0x00000000003800f0 0x000000000003800f

def z99 : W := mkw 0x8028d898fbff15ca 0x88028d898fbff15c 0xe019f9f9ffff3fcf 0x6e019f9f9ffff3fc

def z100 : W := mkw 0x200008004d77b5ee 0x8200008004d77b5e 0xe00000003ffffff0 0x2e00000003ffffff

def z101 : W := mkw 0x0248d7ff80000000 0x10248d7ff8000000 0x0019ffffc000000f 0x40019ffffc000000

def z102 : W := mkw 0x06c767cf00000000 0x006c767cf0000000 0x1fe7ffcfc000000f 0xd1fe7ffcfc000000

def z103 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee01c7803c07f009 0xfee01c7803c07f00

def z104 : W := mkw 0x260dd59c8c57b1ac 0x8260dd59c8c57b1a 0xee1fc7be3cfff3fd 0xfee1fc7be3cfff3f

def z105 : W := mkw 0x9d1d980019f60000 0x09d1d980019f6000 0x4e19f8001fe70007 0x74e19f8001fe7000

def z106 : W := mkw 0x26e76fcf6f3dfcff 0x026e76fcf6f3dfcf 0xffe7ffcfff3ffcff 0xfffe7ffcfff3ffcf

def z107 : W := mkw 0x020005000400a000 0x0020005000400a00 0xee06078e3c38f0fd 0xfee06078e3c38f0f

def z108 : W := mkw 0x14cff2df80000000 0x114cff2df8000000 0x11e7fe4fc000000e 0xc11e7fe4fc000000

def z109 : W := mkw 0x00200800636b5ddb 0x800200800636b5dd 0xe000000023fffff0 0x2e000000023fffff

def z110 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11fe3e7fc000000e 0xc11fe3e7fc000000

def z111 : W := mkw 0x0040024340004c53 0x00040024340004c5 0x2000064fc000ccf8 0x02000064fc000ccf

def z112 : W := mkw 0xcb700f603ffeea00 0x0cb700f603ffeea0 0xfff807f03fffff0b 0xffff807f03fffff0

def z113 : W := mkw 0x5ffff7ffb680ea00 0x15ffff7ffb680ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z114 : W := mkw 0x4bf227633680ea00 0x04bf227633680ea0 0xfffe3fffffc0ff0f 0xffffe3fffffc0ff0

def z115 : W := mkw 0x04a728002b3c0000 0x004a728002b3c000 0xdfe7f8003f3f0007 0xfdfe7f8003f3f000

def z116 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x11e63e4fc3000c0e 0xc11e63e4fc3000c0

def z117 : W := mkw 0x020005000400a000 0x0020005000400a00 0x4e0001801c003001 0x14e0001801c00300

def z118 : W := mkw 0x5ffff7ffb2804a00 0x15ffff7ffb2804a0 0x1fffffffc3c00f0f 0xd1fffffffc3c00f0

def z119 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0x8e07c60e3c3fc0f4 0x98e07c60e3c3fc0f

def z120 : W := mkw 0x1d1d900000000000 0x01d1d90000000000 0x0e19c00000000001 0x10e19c0000000000

def z121 : W := mkw 0x0248dfffc16315ca 0x90248dfffc16315c 0x6019ffffc3e73fcf 0x66019ffffc3e73fc

def z122 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xdff806003fc0c003 0xfdff806003fc0c00

def z123 : W := mkw 0x1fdfb76000000000 0x01fdfb7600000000 0x1ffffff00000000f 0xd1ffffff00000000

def z124 : W := mkw 0x948ff898c97f15ca 0x8948ff898c97f15c 0x601ff9f9c3ff3fcf 0x6601ff9f9c3ff3fc

def z125 : W := mkw 0x0008d09880431188 0x80008d0988043118 0x4019c1b000c73301 0x04019c1b000c7330

def z126 : W := mkw 0x3fd727670c14a024 0x13fd727670c14a02 0x9fe606063c18c030 0x99fe606063c18c03

def z127 : W := mkw 0x9fffffffbbfe0000 0x19fffffffbbfe000 0xdfffffffffff000f 0xfdfffffffffff000

def z128 : W := mkw 0x0082280341280453 0x0008228034128045 0xa0063e0fe038c0fc 0xea0063e0fe038c0f

def z129 : W := mkw 0x00c2224300000000 0x000c222430000000 0xb1e63e4fe038c0fe 0xeb1e63e4fe038c0f

def z130 : W := mkw 0x260505040c14a024 0x0260505040c14a02 0xae06060e3c38c0fc 0xfae06060e3c38c0f

def z131 : W := mkw 0x0930000032800000 0x0093000003280000 0xdff800003fc00003 0xfdff800003fc0000

def z132 : W := mkw 0x1fdff7ff88140000 0x11fdff7ff8814000 0xdffffffffc3f000f 0xfdffffffffc3f000

def z133 : W := mkw 0x9dbfb8007bfe0442 0x09dbfb8007bfe044 0xfffff849ffff0ccf 0xffffff849ffff0cc

def z134 : W := mkw 0x49789a70f3e24f42 0x849789a70f3e24f4 0x11f83871c3c00f02 0x011f83871c3c00f0

def z135 : W := mkw 0x1f1dd5bc80000000 0x11f1dd5bc8000000 0x0e1fc7be0000000d 0xd0e1fc7be0000000

def z136 : W := mkw 0x0060024022004800 0x0006002402200480 0xb1e006402300cc0a 0xeb1e006402300cc0

def z137 : W := mkw 0x4b1005201480a200 0x04b1005201480a20 0x4e1801b01cc03301 0x14e1801b01cc0330

def z138 : W := mkw 0x0605458c0400a000 0x00605458c0400a00 0xee07c78e3c00f00d 0xfee07c78e3c00f00

def z139 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x7fffffffc3c03f0f 0xf7fffffffc3c03f0

def z140 : W := mkw 0x1fdff7ffc00115ca 0x91fdff7ffc00115c 0x3fffffffc0003fcf 0xd3fffffffc0003fc

def z141 : W := mkw 0x0b5007600400a000 0x00b5007600400a00 0xfff807f03c00f00b 0xffff807f03c00f00

def z142 : W := mkw 0x6f7547ec3e95faac 0x06f7547ec3e95faa 0xffffc7fe3fffffff 0xfffffc7fe3ffffff

def z143 : W := mkw 0x9918900010c20000 0x09918900010c2000 0x0018000000c00000 0x00018000000c0000

def z144 : W := mkw 0x2200459cc401b5ee 0x82200459cc401b5e 0x200007ffc000fff8 0x0200007ffc000fff

def z145 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1fe7fe0fc0000004 0x91fe7fe0fc000000

def z146 : W := mkw 0x9db720003a9c0000 0x09db720003a9c000 0xdffe00003fd80003 0xfdffe00003fd8000

def z147 : W := mkw 0x99faba73b3ea0000 0x199faba73b3ea000 0x11f83871c3c00002 0x011f83871c3c0000

def z148 : W := mkw 0x9d3d90003ad60000 0x09d3d90003ad6000 0xdff9c0003fc70003 0xfdff9c0003fc7000

def z149 : W := mkw 0x0950026000000000 0x0095002600000000 0x11f8007000000002 0x011f800700000000

def z150 : W := mkw 0x0040027380000000 0x1004002738000000 0x00000071c0000000 0x000000071c000000

def z151 : W := mkw 0x0605458c08140000 0x00605458c0814000 0xce07c78e3c3f000d 0xfce07c78e3c3f000

def z152 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee1fc7fe3fffffff 0xfee1fc7fe3ffffff

def z153 : W := mkw 0x0405000008140000 0x0040500000814000 0xee07c60e3c3fc0fd 0xfee07c60e3c3fc0f

def z154 : W := mkw 0x19dafafbc16315ca 0x919dafafbc16315c 0x71f9f9f9c3e73fcf 0x671f9f9f9c3e73fc

def z155 : W := mkw 0xbf1dd58c1cd7b0ac 0x0bf1dd58c1cd7b0a 0x4e19c1801cc73001 0x14e19c1801cc7300

def z156 : W := mkw 0x40e22a4377a8ee53 0x040e22a4377a8ee5 0xf1e63e4ffff8fffe 0xef1e63e4ffff8fff

def z157 : W := mkw 0x0000080041200442 0x0000008004120044 0x00003841c3000c02 0x000003841c3000c0

def z158 : W := mkw 0xdfffbf603ffeea00 0x0dfffbf603ffeea0 0xfffffff03fffff0f 0xffffffff03fffff0

def z159 : W := mkw 0x5bfab773b680ea00 0x15bfab773b680ea0 0xfff83ff1ffc0ff0b 0xffff83ff1ffc0ff0

def z160 : W := mkw 0x2405408c081510ac 0x02405408c081510a 0x0007c00e003f00f4 0x00007c00e003f00f

def z161 : W := mkw 0x3fdff7ff8401b0ac 0x13fdff7ff8401b0a 0x3fffffffc000f0ff 0xd3fffffffc000f0f

def z162 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x4019f9f1c3c73f03 0x04019f9f1c3c73f0

def z163 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e03841c0000002 0x011e03841c000000

def z164 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x0019f9f9c02700cf 0x40019f9f9c02700c

def z165 : W := mkw 0x2208dd9cc563b5ee 0x82208dd9cc563b5e 0x6019ffffc3e7ffff 0x66019ffffc3e7fff

def z166 : W := mkw 0x948fb800097e0000 0x0948fb800097e000 0x401ff80003ff0007 0x6401ff80003ff000

def z167 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00006002000c008 0xea00006002000c00

def z168 : W := mkw 0x2008d898cd77b5ee 0x82008d898cd77b5e 0xe019f9f9ffffffff 0x6e019f9f9fffffff

def z169 : W := mkw 0x00004098c00115ca 0x800004098c00115c 0x6001c1f9c0273fcd 0x66001c1f9c0273fc

def z170 : W := mkw 0x94efba436b7e4c53 0x094efba436b7e4c5 0xb1e7fe4fe33fccfe 0xeb1e7fe4fe33fccf

def z171 : W := mkw 0x1fd7276700000000 0x11fd727670000000 0x1fe63e4fc000000e 0xd1fe63e4fc000000

def z172 : W := mkw 0x0040024300000000 0x0004002430000000 0x0000064fc0000008 0x00000064fc000000

def z173 : W := mkw 0x4b700f6077a8ee53 0x04b700f6077a8ee5 0xfff807f03ff8fffb 0xffff807f03ff8fff

def z174 : W := mkw 0x00e2224322004800 0x000e222432200480 0xb1e63e4fe300cc0e 0xeb1e63e4fe300cc0

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0x4001c00000270005 0x64001c0000027000

def z176 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x9ffe38003fd80002 0x99ffe38003fd8000

def z177 : W := mkw 0x99bab810f3ea0542 0x899bab810f3ea054 0x11f83871c3c00f02 0x011f83871c3c00f0

def z178 : W := mkw 0x0008d09880431188 0x80008d0988043118 0x6019c1f003c73f0b 0x66019c1f003c73f0

def z179 : W := mkw 0x00a2280023280000 0x000a228002328000 0x91e6380023380006 0xe91e638002338000

def z180 : W := mkw 0x3f9ff58c0c15b0ac 0x03f9ff58c0c15b0a 0xffffff8e3c3ff0ff 0xfffffff8e3c3ff0f

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x0006000e003800f4 0x00006000e003800f

def z182 : W := mkw 0x0082280341280453 0x0008228034128045 0x0006380fc03800f4 0x00006380fc03800f

def z183 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1fffc7b600000001 0x91fffc7b60000000

def z184 : W := mkw 0x4bf227633688ea11 0x04bf227633688ea1 0xfffe07f63fd8ff3b 0xffffe07f63fd8ff3

def z185 : W := mkw 0x402000003680ea00 0x0402000003680ea0 0x800000003c00c000 0x0800000003c00c00

def z186 : W := mkw 0x0020000022000000 0x0002000002200000 0x91e0000023000002 0xe91e000002300000

def z187 : W := mkw 0x19faba73e3284c53 0x119faba73e3284c5 0xb1fe3e7fe338ccfe 0xeb1fe3e7fe338ccf

def z188 : W := mkw 0x168ff59f80000000 0x1168ff59f8000000 0x0e07ff8fc000000d 0xd0e07ff8fc000000

def z189 : W := mkw 0x2f35458c3e95b0ac 0x02f35458c3e95b0a 0xffffc78e3ffff0ff 0xfffffc78e3ffff0f

def z190 : W := mkw 0x0605458c00000000 0x00605458c0000000 0xae07c78e2038c0fd 0xfae07c78e2038c0f

def z191 : W := mkw 0x00e22a4323280000 0x000e22a432328000 0x91e63e4fe338000e 0xe91e63e4fe338000

def z192 : W := mkw 0xa02008003fffb0ac 0x0a02008003fffb0a 0xe00000003ffff0f0 0x2e00000003ffff0f

def z193 : W := mkw 0x00eafadbe3284c53 0x000eafadbe3284c5 0xb1ffffffe338ccff 0xeb1ffffffe338ccf

def z194 : W := mkw 0x220005040400a024 0x0220005040400a02 0x000006060000c030 0x0000006060000c03

def z195 : W := mkw 0x0008d098c04315ca 0x80008d098c04315c 0x6019c1f9c0c73fc9 0x06019c1f9c0c73fc

def z196 : W := mkw 0x000000000400a000 0x0000000000400a00 0xe00000003c00f000 0x2e00000003c00f00

def z197 : W := mkw 0x0000000000000000 0x0000000000000000 0x001801f00000000b 0x4001801f00000000

def z198 : W := mkw 0x0060024022004800 0x0006002402200480 0xb1e6064e2338ccfe 0xeb1e6064e2338ccf

def z199 : W := mkw 0x0060024022004800 0x0006002402200480 0xf1f807f023c0ff0b 0xef1f807f023c0ff0

def z200 : W := mkw 0x0008900000420000 0x0000890000042000 0x4019c00000c70001 0x04019c00000c7000

def z201 : W := mkw 0x0605458c00000000 0x00605458c0000000 0x0e01c18000000001 0x10e01c1800000000

def z202 : W := mkw 0x1bdaf7ff80000000 0x11bdaf7ff8000000 0x11f83fffc000000a 0x011f83fffc000000

def z203 : W := mkw 0x9db728003bbc0000 0x09db728003bbc000 0x9fe638003f380006 0xf9fe638003f38000

def z204 : W := mkw 0x2405000408140024 0x0240500040814002 0x0006000600180030 0x0000600060018003

def z205 : W := mkw 0x200000000c15b0ac 0x0200000000c15b0a 0xe00000003c3ff0f0 0x2e00000003c3ff0f

def z206 : W := mkw 0x59fab273b2804a00 0x159fab273b2804a0 0x11f83871c3c00f02 0x011f83871c3c00f0

def z207 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x2001f9f9c0273fcc 0x02001f9f9c0273fc

def z208 : W := mkw 0x00a2200022080000 0x000a220002208000 0x91e6000020180000 0x891e600002018000

def z209 : W := mkw 0x00004098c00115ca 0x800004098c00115c 0x200001f9c0003fc8 0x0200001f9c0003fc

def z210 : W := mkw 0x224047ff8401b0ac 0x1224047ff8401b0a 0x200007ffc000f0f8 0x0200007ffc000f0f

def z211 : W := mkw 0x0008d09880000000 0x00008d0988000000 0x6019f9f9c3c03f0f 0x66019f9f9c3c03f0

def z212 : W := mkw 0x148fb00000000000 0x0148fb0000000000 0x0007f80000000004 0x00007f8000000000

def z213 : W := mkw 0x008af89bc16b15db 0x8008af89bc16b15d 0x0007f80fc03f00f4 0x00007f80fc03f00f

def z214 : W := mkw 0x4b1005201480a200 0x04b1005201480a20 0x0e0000001c000000 0x10e0000001c00000

def z215 : W := mkw 0x0605458c00000000 0x00605458c0000000 0x0e07c78e0000000d 0xd0e07c78e0000000

def z216 : W := mkw 0x0000408800011088 0x0000040880001108 0x6019c1f803e73fcf 0x66019c1f803e73fc

def z217 : W := mkw 0x202008006f3dfcff 0x0202008006f3dfcf 0xe00000003f3ffcf0 0x2e00000003f3ffcf

def z218 : W := mkw 0x00e22a43636b5ddb 0x800e22a43636b5dd 0xf1e63e4fe3fffffe 0xef1e63e4fe3fffff

def z219 : W := mkw 0x0000080041620542 0x8000008004162054 0x0000000003c00f00 0x00000000003c00f0

def z220 : W := mkw 0x4bf22f6377a8ee53 0x04bf22f6377a8ee5 0xbfe63e4fff38ccfe 0xfbfe63e4fff38ccf

def z221 : W := mkw 0x4970026032804a00 0x04970026032804a0 0x11e0000000000000 0x011e000000000000

def z222 : W := mkw 0x0082280341280453 0x0008228034128045 0x2006384fc3380cfe 0x62006384fc3380cf

def z223 : W := mkw 0x00cafadbc16315ca 0x800cafadbc16315c 0x71ffffffc3e73fcf 0xe71ffffffc3e73fc

def z224 : W := mkw 0x99faba4373ea4c53 0x099faba4373ea4c5 0xb1fe3e4fe3f8ccfe 0xeb1fe3e4fe3f8ccf

def z225 : W := mkw 0x0008901080000000 0x0000890108000000 0x00183871c0000002 0x000183871c000000

def z226 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0xe01fffffe3ffffff 0xee01fffffe3fffff

def z227 : W := mkw 0x9d1d900018d60000 0x09d1d900018d6000 0xce1fc0003cff0005 0xfce1fc0003cff000

def z228 : W := mkw 0x3f1dd5bc8c15b0ac 0x13f1dd5bc8c15b0a 0x4e19c1b01c073001 0x14e19c1b01c07300

def z229 : W := mkw 0x842508003bfe0000 0x0842508003bfe000 0xce07c0003fff0005 0xfce07c0003fff000

def z230 : W := mkw 0x0bf22f6363284c53 0x00bf22f6363284c5 0xbffe3fffe338ccff 0xfbffe3fffe338ccf

def z231 : W := mkw 0x3fd767ef0c15b0ac 0x13fd767ef0c15b0a 0xffe7c78e3c3ff0fd 0xfffe7c78e3c3ff0f

def z232 : W := mkw 0x94afb8003bfe0000 0x094afb8003bfe000 0xc007f8003fff0004 0x2c007f8003fff000

def z233 : W := mkw 0x1fdfffffc1200442 0x11fdfffffc120044 0x3fffffffc3200ccf 0xf3fffffffc3200cc

def z234 : W := mkw 0x0000000000000000 0x0000000000000000 0x00003849c000000e 0x400003849c000000

def z235 : W := mkw 0x4b18ddb8d5e3b7ca 0x84b18ddb8d5e3b7c 0x6e19f9f9dfe73fcf 0x76e19f9f9dfe73fc

def z236 : W := mkw 0x0200458c00000000 0x00200458c0000000 0x0000078e00000008 0x00000078e0000000

def z237 : W := mkw 0x3fdff7ff8c14a024 0x13fdff7ff8c14a02 0x9ffffffffc18c03f 0xd9ffffffffc18c03

def z238 : W := mkw 0x1d9fb00008140000 0x01d9fb0000814000 0xdffff8003c3f0007 0xfdffff8003c3f000

def z239 : W := mkw 0x00e2224322084811 0x000e222432208481 0xb1e6060e2038c0fc 0xeb1e6060e2038c0f

def z240 : W := mkw 0x0930000032800000 0x0093000003280000 0xfff801f03fc03f0b 0xffff801f03fc03f0

def z241 : W := mkw 0x9fffffffb3ea0000 0x19fffffffb3ea000 0x1fffffffc3c0000f 0xd1fffffffc3c0000

def z242 : W := mkw 0xbfffffffbfffb0ac 0x1bfffffffbfffb0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z243 : W := mkw 0xa6254d8c3fffb0ac 0x0a6254d8c3fffb0a 0xee07c78e3ffff0fd 0xfee07c78e3ffff0f

def z244 : W := mkw 0x4978daf8f3e35fca 0x84978daf8f3e35fc 0x71f9f9f9c3e73fcf 0x671f9f9f9c3e73fc

def z245 : W := mkw 0x148ff09f80000000 0x1148ff09f8000000 0x001ff9ffc000000f 0x4001ff9ffc000000

def z246 : W := mkw 0x5ffffffff7a8ee53 0x15ffffffff7a8ee5 0xfffffffffff8ffff 0xffffffffffff8fff

def z247 : W := mkw 0x0000000040004c53 0x00000000040004c5 0x200000000000ccf0 0x0200000000000ccf

def z248 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0x5ff801f01fc03f03 0x15ff801f01fc03f0

def z249 : W := mkw 0x80e22a437bfe4c53 0x080e22a437bfe4c5 0xf1e63e4fffffccfe 0xef1e63e4fffffccf

def z250 : W := mkw 0xdff727603e9cea00 0x0dff727603e9cea0 0x9fe606003c18c000 0x99fe606003c18c00

def z251 : W := mkw 0x9db720003a9c0000 0x09db720003a9c000 0xdfe7c0003c3f0005 0xfdfe7c0003c3f000

def z252 : W := mkw 0x1ff7276722084811 0x11ff727672208481 0x9fe606062018c030 0x99fe606062018c03

def z253 : W := mkw 0x0060024022004800 0x0006002402200480 0x91e006002000c000 0x891e006002000c00

def z254 : W := mkw 0x0b70076022004800 0x00b7007602200480 0xbff807f02300cc0b 0xfbff807f02300cc0

def z255 : W := mkw 0x224047cf4401fcff 0x0224047cf4401fcf 0x200007cfc000fcf8 0x0200007cfc000fcf

def z256 : W := mkw 0x1f9ff5bf80000000 0x11f9ff5bf8000000 0x0e1ff9bfc0000005 0x10e1ff9bfc000000

def z257 : W := mkw 0x148ff89fc16315ca 0x9148ff89fc16315c 0x601ff9ffc3e73fcf 0x6601ff9ffc3e73fc

def z258 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z259 : W := mkw 0x1fdff7ff80011088 0x11fdff7ff8001108 0x7fffffffc02730cf 0xf7fffffffc02730c

def z260 : W := mkw 0x148ff89fc16315ca 0x9148ff89fc16315c 0x0007f80fc02700c4 0x00007f80fc02700c

def z261 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xce07c1803c3f3005 0xfce07c1803c3f300

def z262 : W := mkw 0x2f5547ec0c15b0ac 0x02f5547ec0c15b0a 0xffffc7fe3c3ff0ff 0xfffffc7fe3c3ff0f

def z263 : W := mkw 0x99baf898f3eb15ca 0x899baf898f3eb15c 0x71f9f9f9c3e73fcf 0x671f9f9f9c3e73fc

def z264 : W := mkw 0x00400a4341204c53 0x000400a4341204c5 0x20003e4fc320ccfe 0x620003e4fc320ccf

def z265 : W := mkw 0x00004898c16315ca 0x800004898c16315c 0x600001f9c3e73fc8 0x2600001f9c3e73fc

def z266 : W := mkw 0x0000080041200442 0x0000008004120044 0x20003849c3200cce 0x620003849c3200cc

def z267 : W := mkw 0x040d980009760000 0x0040d98000976000 0xce1ff8003fff0007 0xfce1ff8003fff000

def z268 : W := mkw 0x26e72f476f3cec77 0x026e72f476f3cec7 0xbfe63e4fff38ccfe 0xfbfe63e4fff38ccf

def z269 : W := mkw 0x424047f8c401ffca 0x8424047f8c401ffc 0x200007f9c000ffc8 0x0200007f9c000ffc

def z270 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x31e03e4fc300ccfa 0x031e03e4fc300ccf

def z271 : W := mkw 0x0008901080420100 0x8000890108042010 0x0018003000c00300 0x00018003000c0030

def z272 : W := mkw 0x0000080001620000 0x0000008000162000 0x4000000003e70000 0x24000000003e7000

def z273 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0xbfffffffe038c0ff 0xfbfffffffe038c0f

def z274 : W := mkw 0x1fffffffe3284c53 0x11fffffffe3284c5 0x1fffffffc3000c0f 0xd1fffffffc3000c0

def z275 : W := mkw 0x0040024000004800 0x0004002400000480 0x200006400000cc08 0x0200006400000cc0

def z276 : W := mkw 0x4b5007601480ea00 0x04b5007601480ea0 0x6e1807f01cc0ff09 0x16e1807f01cc0ff0

def z277 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xae06078e3c18f0f8 0x9ae06078e3c18f0f

def z278 : W := mkw 0x0040024000000000 0x0004002400000000 0x11e006400000000a 0xc11e006400000000

def z279 : W := mkw 0x0082200300000000 0x0008220030000000 0x0006380fc0000004 0x00006380fc000000

def z280 : W := mkw 0x9d3d98003bfe0000 0x09d3d98003bfe000 0xce19c0003fff0001 0x3ce19c0003fff000

def z281 : W := mkw 0x0b70076032800000 0x00b7007603280000 0xdff807f03fc0000b 0xfdff807f03fc0000

def z282 : W := mkw 0x040dd898c97715ca 0x8040dd898c97715c 0xee1ff9f9ffff3fcf 0xfee1ff9f9ffff3fc

def z283 : W := mkw 0x064547ff80000000 0x1064547ff8000000 0x0e07c7ffc000000d 0xd0e07c7ffc000000

def z284 : W := mkw 0x00e22a4023284800 0x000e22a402328480 0xb1e63e402338cc0e 0xeb1e63e402338cc0

def z285 : W := mkw 0x948ff898c97f15ca 0x8948ff898c97f15c 0x0007f809c03f00c4 0x00007f809c03f00c

def z286 : W := mkw 0x00c22a4341284c53 0x000c22a4341284c5 0x20063e4fc038ccfc 0x020063e4fc038ccf

def z287 : W := mkw 0x0008d09880000000 0x00008d0988000000 0x0019f9f9c000000f 0x40019f9f9c000000

def z288 : W := mkw 0x9dbfb8037bfe0453 0x09dbfb8037bfe045 0xdffff80fffff00f7 0xfdffff80fffff00f

def z289 : W := mkw 0x1f1dd5bc80000000 0x11f1dd5bc8000000 0x0e19f9f9c000000f 0x50e19f9f9c000000

def z290 : W := mkw 0xdff727603e9cea00 0x0dff727603e9cea0 0xfffe07f03fd8ff0b 0xffffe07f03fd8ff0

def z291 : W := mkw 0x0020000032800000 0x0002000003280000 0xc00000003fc00000 0x2c00000003fc0000

def z292 : W := mkw 0x00600a4363284c53 0x000600a4363284c5 0xa000064fe338ccf8 0x2a000064fe338ccf

def z293 : W := mkw 0x00089800416315ca 0x800089800416315c 0x6019f80003e73fc7 0x66019f80003e73fc

def z294 : W := mkw 0x1fd767ef00000000 0x11fd767ef0000000 0x1fe7c78e0000000d 0xd1fe7c78e0000000

def z295 : W := mkw 0x2605459ccc15b5ee 0x82605459ccc15b5e 0xee07c7fffc3ffffd 0xfee07c7fffc3ffff

def z296 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e6060600000000 0x811e606060000000

def z297 : W := mkw 0x020045bc80000000 0x1020045bc8000000 0x000001b000000000 0x0000001b00000000

def z298 : W := mkw 0x9d9fb80019fe0000 0x09d9fb80019fe000 0x4e1ff8001cff0005 0x14e1ff8001cff000

def z299 : W := mkw 0x940d900008560000 0x0940d90000856000 0x0001c00000070000 0x00001c0000007000

def z300 : W := mkw 0x99bab80033ea0000 0x099bab80033ea000 0xdff838003fc00003 0xfdff838003fc0000

def z301 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0x9ff807f03c00c00b 0xd9ff807f03c00c00

def z302 : W := mkw 0x020005000400a000 0x0020005000400a00 0xee1807f03fc0ff0b 0xfee1807f03fc0ff0

def z303 : W := mkw 0x0930000032800000 0x0093000003280000 0x9fe000003c000000 0x99fe000003c00000

def z304 : W := mkw 0x4f7547ec3680ea00 0x04f7547ec3680ea0 0xffffc7fe3fc0ff0f 0xfffffc7fe3fc0ff0

def z305 : W := mkw 0x020005000400a000 0x0020005000400a00 0x8e0006003c00c000 0x98e0006003c00c00

def z306 : W := mkw 0x99bab80033ea0000 0x099bab80033ea000 0x51f9f80003e70007 0x651f9f80003e7000

def z307 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xfffff9f03fff3f0f 0xffffff9f03fff3f0

def z308 : W := mkw 0x0020080063284c53 0x00020080063284c5 0x0000000003000c00 0x00000000003000c0

def z309 : W := mkw 0x6b7007603e95faac 0x06b7007603e95faa 0xfff807f03ffffffb 0xffff807f03ffffff

def z310 : W := mkw 0x0d3500003a940000 0x00d3500003a94000 0xdfffc0003fff0007 0xfdfffc0003fff000

def z311 : W := mkw 0x1f1dddbcc16315ca 0x91f1dddbcc16315c 0x6e19f9f9c3e73fcf 0x76e19f9f9c3e73fc

def z312 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000060e0000c0f8 0x02000060e0000c0f

def z313 : W := mkw 0x4020000032804a00 0x04020000032804a0 0x0000000003c00f00 0x00000000003c00f0

def z314 : W := mkw 0x3fdff7ff881510ac 0x13fdff7ff881510a 0x1fffffffc03f00ff 0xd1fffffffc03f00f

def z315 : W := mkw 0x4bfafffbf7ebffdb 0x84bfafffbf7ebffd 0xffffffffffffffff 0xffffffffffffffff

def z316 : W := mkw 0x1ffff7ffa2084811 0x11ffff7ffa208481 0x9fffffffe018c03f 0xd9fffffffe018c03

def z317 : W := mkw 0xb68ffd8c0d7fb0ac 0x0b68ffd8c0d7fb0a 0xee07ff8e3c3ff0fd 0xfee07ff8e3c3ff0f

def z318 : W := mkw 0x0000080041200442 0x0000008004120044 0x2000000003200cc0 0x22000000003200cc

def z319 : W := mkw 0x00e2224322084811 0x000e222432208481 0xb1e606462318cc3a 0xeb1e606462318cc3

def z320 : W := mkw 0x5ffff7ffb680ea00 0x15ffff7ffb680ea0 0x9ffffffffc00c00f 0xd9ffffffffc00c00

def z321 : W := mkw 0x9fdff7ff98d60000 0x19fdff7ff98d6000 0x5fffffffdcc7000f 0xd5fffffffdcc7000

def z322 : W := mkw 0x0910000000000000 0x0091000000000000 0x1ff8000000000003 0xd1ff800000000000

def z323 : W := mkw 0x0008980001620000 0x0000898000162000 0x6019f9f003e73f0f 0x66019f9f003e73f0

def z324 : W := mkw 0x260505040c14a024 0x0260505040c14a02 0x0e0000001c000000 0x10e0000001c00000

def z325 : W := mkw 0x4020080077e3ffca 0x84020080077e3ffc 0xe00000003fe7ffc0 0x2e00000003fe7ffc

def z326 : W := mkw 0x024047ffc0004c53 0x1024047ffc0004c5 0x200007ffc000ccf8 0x0200007ffc000ccf

def z327 : W := mkw 0x09b2280033a80000 0x009b2280033a8000 0xdffe38003ff80007 0xfdffe38003ff8000

def z328 : W := mkw 0x9dbff898bbff1188 0x89dbff898bbff118 0xdffff9b03fff3307 0xfdffff9b03fff330

def z329 : W := mkw 0x00004888412114ca 0x000004888412114c 0x6001f9c9c3273ccf 0x66001f9c9c3273cc

def z330 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0x6e01c78e1c07f0f9 0x16e01c78e1c07f0f

def z331 : W := mkw 0x0008900000000000 0x0000890000000000 0x0019f80000000007 0x40019f8000000000

def z332 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0x9ff806703fc0cf02 0x99ff806703fc0cf0

def z333 : W := mkw 0x9dbfb0003ade0000 0x09dbfb0003ade000 0xdfffc0003cdf0001 0x9dfffc0003cdf000

def z334 : W := mkw 0x0060024022004800 0x0006002402200480 0x11e0004003000c02 0x011e0004003000c0

def z335 : W := mkw 0x0008d09880000000 0x00008d0988000000 0x0019c1b000000001 0x00019c1b00000000

def z336 : W := mkw 0x4bf22f6377a8ee53 0x04bf22f6377a8ee5 0xfff83ff1ffc0ff0b 0xffff83ff1ffc0ff0

def z337 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xdff807b03cc0f301 0x9dff807b03cc0f30

def z338 : W := mkw 0x0240076700000000 0x1024007670000000 0x0000060600000000 0x0000006060000000

def z339 : W := mkw 0x802898003bfe0000 0x0802898003bfe000 0xc019f8003fff0007 0x6c019f8003fff000

def z340 : W := mkw 0x8020080033ea0000 0x08020080033ea000 0x0000000003c00000 0x00000000003c0000

def z341 : W := mkw 0xbdbff88c3bff10ac 0x0bdbff88c3bff10a 0xdffff80e3fff00f7 0xfdffff80e3fff00f

def z342 : W := mkw 0x49f22a6373a84e53 0x049f22a6373a84e5 0xb1fe3e7fe3f8cffe 0xeb1fe3e7fe3f8cff

def z343 : W := mkw 0x0930000032800000 0x0093000003280000 0x11f8000003c00002 0x011f8000003c0000

def z344 : W := mkw 0x9df72a437bbc4c53 0x09df72a437bbc4c5 0xbfe63e4fff38ccfe 0xfbfe63e4fff38ccf

def z345 : W := mkw 0x2200458c0401b0ac 0x02200458c0401b0a 0x6001c78e0027f0fd 0x66001c78e0027f0f

def z346 : W := mkw 0x008af89bc16b15db 0x8008af89bc16b15d 0x601ff9ffc3ff3fff 0x6601ff9ffc3ff3ff

def z347 : W := mkw 0x7ffff7ffbe95faac 0x17ffff7ffbe95faa 0xffffffffffffffff 0xffffffffffffffff

def z348 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x91e63e47e318cc32 0x891e63e47e318cc3

def z349 : W := mkw 0xbfb7658c3e9db0ac 0x0bfb7658c3e9db0a 0xffe7c78e3c3ff0fd 0xfffe7c78e3c3ff0f

def z350 : W := mkw 0x00c2224340004c53 0x000c2224340004c5 0x31e63e4fc000ccfe 0xc31e63e4fc000ccf

def z351 : W := mkw 0x2405408c081510ac 0x02405408c081510a 0x6007c18e003f30fd 0x66007c18e003f30f

def z352 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x11e6384fc3380cf6 0x011e6384fc3380cf

def z353 : W := mkw 0x26054d8c4d77b5ee 0x826054d8c4d77b5e 0xee07c78e3ffffffd 0xfee07c78e3ffffff

def z354 : W := mkw 0x4b3005203680ea00 0x04b3005203680ea0 0xee1801b03fc0ff01 0x3ee1801b03fc0ff0

def z355 : W := mkw 0xbfffffcf7ffffcff 0x0bfffffcf7ffffcf 0xffffffcffffffcff 0xfffffffcffffffcf

def z356 : W := mkw 0x4bf22f6037a8ea00 0x04bf22f6037a8ea0 0xfffe3ff03ff8ff0f 0xffffe3ff03ff8ff0

def z357 : W := mkw 0x09f22a4373a84c53 0x009f22a4373a84c5 0xfffe3e4ffff8ccff 0xffffe3e4ffff8ccf

def z358 : W := mkw 0x024047ffc00115ca 0x9024047ffc00115c 0x200007ffc0003fc8 0x0200007ffc0003fc

def z359 : W := mkw 0x9dbff898fbff15ca 0x89dbff898fbff15c 0xdffff809ffff00c7 0xfdffff809ffff00c

def z360 : W := mkw 0x9dffba73bbfe0000 0x19dffba73bbfe000 0xdffff871ffff0007 0xfdffff871ffff000

def z361 : W := mkw 0x2605458c0c14a024 0x02605458c0c14a02 0x8e07c78e3c18c03d 0xd8e07c78e3c18c03

def z362 : W := mkw 0x0bd2276300000000 0x00bd227630000000 0x1ffe3fffc000000f 0xd1ffe3fffc000000

def z363 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x2001f849c3270cce 0x62001f849c3270cc

def z364 : W := mkw 0x9dbff89fbbfe0000 0x19dbff89fbbfe000 0xdffff80fffff0007 0xfdffff80fffff000

def z365 : W := mkw 0x240500000c15b0ac 0x0240500000c15b0a 0xee07c0003c3ff0f5 0xfee07c0003c3ff0f

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0x0006060e0000000c 0xc0006060e0000000

def z367 : W := mkw 0x0008d09880431188 0x80008d0988043118 0x4019f9f9c0c7330f 0x44019f9f9c0c7330

def z368 : W := mkw 0x5f1dd5bc9480a200 0x15f1dd5bc9480a20 0x4e19c1b01cc03301 0x14e19c1b01cc0330

def z369 : W := mkw 0x9ffff7ffba9c0000 0x19ffff7ffba9c000 0x9ffffffffc18000f 0xd9ffffffffc18000

def z370 : W := mkw 0x8000000018d60000 0x08000000018d6000 0x400000001cc70000 0x0400000001cc7000

def z371 : W := mkw 0x9d9fb00018d60000 0x09d9fb00018d6000 0x5ffff8001cc70007 0xd5ffff8001cc7000

def z372 : W := mkw 0xdfbfbd203ffea200 0x0dfbfbd203ffea20 0xdffff9b03fff3307 0xfdffff9b03fff330

def z373 : W := mkw 0x19d2226300000000 0x119d222630000000 0x11e0000000000000 0x011e000000000000

def z374 : W := mkw 0x00e2224322084811 0x000e222432208481 0x11e0000000000000 0x011e000000000000

def z375 : W := mkw 0x9dffba433bfe0000 0x09dffba433bfe000 0xdffffe4fffff000f 0xfdffffe4fffff000

def z376 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x11fff80003ff0006 0x011fff80003ff000

def z377 : W := mkw 0x24e76acf6b3d5cff 0x024e76acf6b3d5cf 0xb1e7fe4fe33fccfe 0xeb1e7fe4fe33fccf

def z378 : W := mkw 0x1bdab77380000000 0x11bdab7738000000 0x1ff83ff1c000000b 0xd1ff83ff1c000000

def z379 : W := mkw 0x0020000022084811 0x0002000002208481 0x800000002018c030 0x0800000002018c03

def z380 : W := mkw 0x260ddd8c0d77b0ac 0x0260ddd8c0d77b0a 0xee1fff8e3ffff0ff 0xfee1fff8e3ffff0f

def z381 : W := mkw 0x1fdff7ff8400a000 0x11fdff7ff8400a00 0xfffffffffc00f00f 0xffffffffffc00f00

def z382 : W := mkw 0x4040026000004a00 0x04040026000004a0 0x0000007000000f00 0x00000007000000f0

def z383 : W := mkw 0x200000000c14a024 0x0200000000c14a02 0x800000003c18c030 0x0800000003c18c03

def z384 : W := mkw 0x2405408c081510ac 0x02405408c081510a 0x0001c00000070000 0x00001c0000007000

def z385 : W := mkw 0x0970024032804800 0x0097002403280480 0xfff806403fc0cc0b 0xffff806403fc0cc0

def z386 : W := mkw 0x0008d89881631188 0x80008d8988163118 0x4019f9b003e73307 0x64019f9b003e7330

def z387 : W := mkw 0x5fdff7ff8400ea00 0x15fdff7ff8400ea0 0x3fffffffc000ff0f 0xd3fffffffc000ff0

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000004003000c0a 0x62000004003000c0

def z389 : W := mkw 0x220005000c15b0ac 0x0220005000c15b0a 0xee0007803c3ff0f9 0xfee0007803c3ff0f

def z390 : W := mkw 0x0048dadbc1635ddb 0x80048dadbc1635dd 0x6019ffffc3e7ffff 0x66019ffffc3e7fff

def z391 : W := mkw 0x1fd7276700000000 0x11fd727670000000 0x1ffe07f60000000b 0xd1ffe07f60000000

def z392 : W := mkw 0x200000000c15b0ac 0x0200000000c15b0a 0xe006060e3c3ff0fc 0xee006060e3c3ff0f

def z393 : W := mkw 0x424007600400ea00 0x0424007600400ea0 0x601807f003c0ff0b 0x6601807f003c0ff0

def z394 : W := mkw 0x0000000008140000 0x0000000000814000 0xc00000003c3f0000 0x2c00000003c3f000

def z395 : W := mkw 0x0b58dff8c16315ca 0x80b58dff8c16315c 0x7ff9fff9c3e73fcf 0xf7ff9fff9c3e73fc

def z396 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x4019f9b9c0e733c5 0x04019f9b9c0e733c

def z397 : W := mkw 0x400000000400ea00 0x0400000000400ea0 0x200000000000ff00 0x0200000000000ff0

def z398 : W := mkw 0x0f5547ec00000000 0x00f5547ec0000000 0x1fffc7fe0000000f 0xd1fffc7fe0000000

def z399 : W := mkw 0xd9faba6033ea4a00 0x0d9faba6033ea4a0 0x11f8387003c00f02 0x011f8387003c00f0

def z400 : W := mkw 0x0000000040000442 0x0000000004000044 0x20000049c0000cc8 0x020000049c0000cc

def z401 : W := mkw 0x260ddd9ccd77b5ee 0x8260ddd9ccd77b5e 0x6e19f9f9dfe73fcf 0x76e19f9f9dfe73fc

def z402 : W := mkw 0x1ddfb24300000000 0x01ddfb2430000000 0x1ffffe4fc000000f 0xd1ffffe4fc000000

def z403 : W := mkw 0x0240076000000000 0x0024007600000000 0x000007f000000008 0x0000007f00000000

def z404 : W := mkw 0x00aab800236a0000 0x000aab800236a000 0xd1fff80023ff0007 0xed1fff80023ff000

def z405 : W := mkw 0x1918903080000000 0x1191890308000000 0x0018003000000000 0x0001800300000000

def z406 : W := mkw 0x1f5dd7fc80000000 0x11f5dd7fc8000000 0x1ff9c7f00000000b 0xd1ff9c7f00000000

def z407 : W := mkw 0x02e22f436728ec53 0x002e22f436728ec5 0xffe63fcfff38fcff 0xfffe63fcfff38fcf

def z408 : W := mkw 0x0000080041200442 0x0000008004120044 0x00003809c02000c4 0x000003809c02000c

def z409 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xfffffe0e3fffc0ff 0xffffffe0e3fffc0f

def z410 : W := mkw 0x02c267ff80000000 0x102c267ff8000000 0x11e63fffc000000e 0xc11e63fffc000000

def z411 : W := mkw 0x260505040c15b0ac 0x0260505040c15b0a 0xee0606063c3ff0f0 0xbee0606063c3ff0f

def z412 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0x5fffffffdc07300f 0xd5fffffffdc07300

def z413 : W := mkw 0xc02008003ffeea00 0x0c02008003ffeea0 0xe00000003fffff00 0x2e00000003fffff0

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x401801b000c03301 0x0401801b000c0330

def z415 : W := mkw 0x99faba4373ea4c53 0x099faba4373ea4c5 0x11f83841c3c00c02 0x011f83841c3c00c0

def z416 : W := mkw 0x0605458c00011088 0x00605458c0001108 0x6e07c78e002730cd 0xf6e07c78e002730c

def z417 : W := mkw 0xbfb725043e9ca024 0x0bfb725043e9ca02 0x9fe606063c18c030 0x99fe606063c18c03

def z418 : W := mkw 0x4b18d5b894c3b388 0x84b18d5b894c3b38 0x4e19c1b01cc73301 0x14e19c1b01cc7330

def z419 : W := mkw 0x42e22f636728ee53 0x042e22f636728ee5 0xb1e63fffe338fffe 0xeb1e63fffe338fff

def z420 : W := mkw 0x6f1545ac1c95b2ac 0x06f1545ac1c95b2a 0xee1fc7be3cfff3fd 0xfee1fc7be3cfff3f

def z421 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0x31f807f003c0ff0a 0x031f807f003c0ff0

def z422 : W := mkw 0x0000000000000000 0x0000000000000000 0x800606062018c030 0x8800606062018c03

def z423 : W := mkw 0x9ffffffffbfe4c53 0x19ffffffffbfe4c5 0xffffffffffffccff 0xfffffffffffffccf

def z424 : W := mkw 0x9ffffffffbff15ca 0x99ffffffffbff15c 0xffffffffffff3fcf 0xfffffffffffff3fc

def z425 : W := mkw 0x026007402600e800 0x0026007402600e80 0xffe007c03f00fc0b 0xfffe007c03f00fc0

def z426 : W := mkw 0x00000800416315ca 0x800000800416315c 0x60003849c3e73fce 0x660003849c3e73fc

def z427 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000002038c0f0 0x2a00000002038c0f

def z428 : W := mkw 0x108ab01380000000 0x1108ab0138000000 0x00003801c0000000 0x000003801c000000

def z429 : W := mkw 0x664547ec0c15faac 0x0664547ec0c15faa 0xee07c7fe3c3ffffd 0xfee07c7fe3c3ffff

def z430 : W := mkw 0x2487688f493d14ff 0x02487688f493d14f 0x0007f80fc03f00f4 0x00007f80fc03f00f

def z431 : W := mkw 0x4910002010800200 0x0491000201080020 0x0018003000c00300 0x00018003000c0030

def z432 : W := mkw 0x6f7507643e94ea24 0x06f7507643e94ea2 0x9fe606063c18c030 0x99fe606063c18c03

def z433 : W := mkw 0x04e72a436b3c4c53 0x004e72a436b3c4c5 0xffe7fe4fff3fccff 0xfffe7fe4fff3fccf

def z434 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xffe006003fc0ff00 0xbffe006003fc0ff0

def z435 : W := mkw 0x1f1dd5bc80431188 0x91f1dd5bc8043118 0x4e19c1b000c73301 0x14e19c1b000c7330

def z436 : W := mkw 0x9dbff8883bff1088 0x09dbff8883bff108 0xfffff9883fff30cf 0xffffff9883fff30c

def z437 : W := mkw 0xbfbffd8c3fffb0ac 0x0bfbffd8c3fffb0a 0xdffff9803fff3007 0xfdffff9803fff300

def z438 : W := mkw 0x00a2280063280442 0x000a228006328044 0xb1e63849e3380cce 0xeb1e63849e3380cc

def z439 : W := mkw 0x400000001480a200 0x0400000001480a20 0x400000001cc03300 0x0400000001cc0330

def z440 : W := mkw 0x26e727472e1ce835 0x026e727472e1ce83 0x9fe606063c18c030 0x99fe606063c18c03

def z441 : W := mkw 0x1487200700000000 0x1148720070000000 0x0006000600000000 0x0000600060000000

def z442 : W := mkw 0x00004098c00115ca 0x800004098c00115c 0x00000009c00000c0 0x000000009c00000c

def z443 : W := mkw 0x26c767cf0c15b0ac 0x026c767cf0c15b0a 0xffe7ffcffc3ff0ff 0xfffe7ffcffc3ff0f

def z444 : W := mkw 0x368ff59f8c15b0ac 0x1368ff59f8c15b0a 0xee07ff8ffc3ff0fd 0xfee07ff8ffc3ff0f

def z445 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0x4e07c18e1c3f30f5 0x14e07c18e1c3f30f

def z446 : W := mkw 0x26876d8f4d3db4ff 0x026876d8f4d3db4f 0xee07ff8ffc3ff0fd 0xfee07ff8ffc3ff0f

def z447 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0x6e01c1881c2730cd 0x76e01c1881c2730c

def z448 : W := mkw 0x060dd59c80000000 0x0060dd59c8000000 0x0e1fffffc000000f 0xd0e1fffffc000000

def z449 : W := mkw 0x4b7047f8f681ffca 0x84b7047f8f681ffc 0xfff807f9ffc0ffcb 0xffff807f9ffc0ffc

def z450 : W := mkw 0x9dffba437bfe4c53 0x09dffba437bfe4c5 0xdffff841ffff0c07 0xfdffff841ffff0c0

def z451 : W := mkw 0x9dffba403bfe4800 0x09dffba403bfe480 0xfffffe403fffcc0f 0xffffffe403fffcc0

def z452 : W := mkw 0x2200458c0401b0ac 0x02200458c0401b0a 0xa006078e2038f0fc 0xea006078e2038f0f

def z453 : W := mkw 0x1ffff7ffa2004800 0x11ffff7ffa200480 0xbfffffffe300cc0f 0xfbfffffffe300cc0

def z454 : W := mkw 0x26efffdfef7ffdff 0x826efffdfef7ffdf 0xffffffffffffffff 0xffffffffffffffff

def z455 : W := mkw 0x1fdfffff81620000 0x11fdfffff8162000 0x5fffffffc3e7000f 0xf5fffffffc3e7000

def z456 : W := mkw 0xdf7d97603ed6ea00 0x0df7d97603ed6ea0 0xfff9c7f03fc7ff0b 0xffff9c7f03fc7ff0

def z457 : W := mkw 0x00a2280023280000 0x000a228002328000 0xb1e63e0e2338c0fe 0xeb1e63e0e2338c0f

def z458 : W := mkw 0x9fffbf673bfe0000 0x19fffbf673bfe000 0xdffffe063fff0007 0xfdffffe063fff000

def z459 : W := mkw 0x140dd09c80000000 0x1140dd09c8000000 0x0001c00000000000 0x00001c0000000000

def z460 : W := mkw 0x4020080077a8ee53 0x04020080077a8ee5 0xe00000003ff8fff0 0x2e00000003ff8fff

def z461 : W := mkw 0x0008980041620442 0x0000898004162044 0x6019f849c3e70ccf 0x66019f849c3e70cc

def z462 : W := mkw 0x06e76fcf63284c53 0x006e76fcf63284c5 0xbfe7ffcfe338ccff 0xfbfe7ffcfe338ccf

def z463 : W := mkw 0x0405000000000000 0x0040500000000000 0x0e07c00000000005 0xd0e07c0000000000

def z464 : W := mkw 0x1f9ff58c00000000 0x01f9ff58c0000000 0x1fffff8e0000000f 0xd1fffff8e0000000

def z465 : W := mkw 0x9dbfb8007bfe4c53 0x09dbfb8007bfe4c5 0xfffff8003fffccf7 0xffffff8003fffccf

def z466 : W := mkw 0x060ddd9cc16315ca 0x8060ddd9cc16315c 0x6e1fffffc3e73fcf 0xf6e1fffffc3e73fc

def z467 : W := mkw 0x0000409880000000 0x0000040988000000 0x000001f9c0000008 0x0000001f9c000000

def z468 : W := mkw 0x0405000008140000 0x0040500000814000 0x8e0600003c180000 0x98e0600003c18000

def z469 : W := mkw 0x00eafadbe36b5ddb 0x800eafadbe36b5dd 0x71f9f9f9c3e73fcf 0x671f9f9f9c3e73fc

def z470 : W := mkw 0x4b7007637680ee53 0x04b7007637680ee5 0xfff807ffffc0fffb 0xffff807ffffc0fff

def z471 : W := mkw 0x4970026032804a00 0x04970026032804a0 0xdff800703fc00f03 0xfdff800703fc00f0

def z472 : W := mkw 0x802008007bff15ca 0x8802008007bff15c 0xe00000003fff3fc0 0x2e00000003fff3fc

def z473 : W := mkw 0x260dd59c8c15b0ac 0x0260dd59c8c15b0a 0xee1ffffffc3ff0ff 0xfee1ffffffc3ff0f

def z474 : W := mkw 0x1d9fb80001620000 0x01d9fb8000162000 0x5ffff80003e70007 0xf5ffff80003e7000

def z475 : W := mkw 0x3fdfffffcd77b5ee 0x93fdfffffcd77b5e 0xffffffffffffffff 0xffffffffffffffff

def z476 : W := mkw 0x260505040c14a024 0x0260505040c14a02 0xce07c6063c3fc035 0xfce07c6063c3fc03

def z477 : W := mkw 0x00600a4063204c42 0x000600a4063204c4 0xb1e03e49e320ccce 0xeb1e03e49e320ccc

def z478 : W := mkw 0xdfffbf603ffeea00 0x0dfffbf603ffeea0 0xdffffe003fffc007 0xfdffffe003fffc00

def z479 : W := mkw 0x422005003680ea00 0x0422005003680ea0 0xee0007803fc0ff09 0xfee0007803fc0ff0

def z480 : W := mkw 0x426007603680ea00 0x0426007603680ea0 0xe00007f03fc0ff08 0x2e00007f03fc0ff0

def z481 : W := mkw 0x0040024340004c53 0x00040024340004c5 0x00000041c0000c00 0x000000041c0000c0

def z482 : W := mkw 0x497002603680ea00 0x0497002603680ea0 0xf1f800703fc0ff02 0x2f1f800703fc0ff0

def z483 : W := mkw 0x493000003680ea00 0x0493000003680ea0 0xfff800003fc0ff03 0xffff800003fc0ff0

def z484 : W := mkw 0x0008d098c00115ca 0x80008d098c00115c 0x2019f9f9c0003fcf 0x42019f9f9c0003fc

def z485 : W := mkw 0x1f15052400000000 0x11f1505240000000 0x0e00000000000000 0x10e0000000000000

def z486 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ff9f9f1c0000003 0x11ff9f9f1c000000

def z487 : W := mkw 0x6ff76fef7fbdfeff 0x06ff76fef7fbdfef 0xffffffffffffffff 0xffffffffffffffff

def z488 : W := mkw 0x5ff727673680ea00 0x15ff727673680ea0 0x9fe606063c00c000 0x99fe606063c00c00

def z489 : W := mkw 0x4b78d7f8b680ea00 0x04b78d7f8b680ea0 0xfff9fff9ffc0ff0f 0xffff9fff9ffc0ff0

def z490 : W := mkw 0x1d9ff898c16315ca 0x81d9ff898c16315c 0x7ffff9f9c3e73fcf 0xf7ffff9f9c3e73fc

def z491 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0x2007c78e003ff0fc 0x02007c78e003ff0f

def z492 : W := mkw 0x9fdfffff897e0000 0x19fdfffff897e000 0x1fffffffc03f000f 0xd1fffffffc03f000

def z493 : W := mkw 0x9d15000018940000 0x09d1500001894000 0x0e0000001c000000 0x10e0000001c00000

def z494 : W := mkw 0x80000800097e0000 0x080000800097e000 0x00000000003f0000 0x000000000003f000

def z495 : W := mkw 0x1fd767ff80000000 0x11fd767ff8000000 0x1fe607ffc0000008 0x91fe607ffc000000

def z496 : W := mkw 0x5f7dd7fcb680ea00 0x15f7dd7fcb680ea0 0xfff9c7f03fc0ff0b 0xffff9c7f03fc0ff0

def z497 : W := mkw 0x4b7047ffb680ea00 0x14b7047ffb680ea0 0xfff807ffffc0ff0b 0xffff807ffffc0ff0

def z498 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x91e63841e3380c06 0xe91e63841e3380c0

def z499 : W := mkw 0x0028d898e36b5ddb 0x80028d898e36b5dd 0xe019f9f9e3ffffff 0x6e019f9f9e3fffff

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0xce0000003c000001 0xfce0000003c00000

def z501 : W := mkw 0x200040880c15b0ac 0x0200040880c15b0a 0xe001c1883c3ff0fd 0x6e001c1883c3ff0f

def z502 : W := mkw 0x9df722433a9c4811 0x09df722433a9c481 0x9fe606063c18c030 0x99fe606063c18c03

def z503 : W := mkw 0x802008007bfe4c53 0x0802008007bfe4c5 0xe00000003fffccf0 0x2e00000003fffccf

def z504 : W := mkw 0x1fdff7ffc0004c53 0x11fdff7ffc0004c5 0x3fffffffc000ccff 0xd3fffffffc000ccf

def z505 : W := mkw 0x6625458c3e95faac 0x06625458c3e95faa 0xee07c78e3ffffffd 0xfee07c78e3ffffff

def z506 : W := mkw 0x6f7547ec3e95faac 0x06f7547ec3e95faa 0xffe7c78e3c3ff0fd 0xfffe7c78e3c3ff0f

def z507 : W := mkw 0x948fb803497e0453 0x0948fb803497e045 0x0007f80fc03f00f4 0x00007f80fc03f00f

def z508 : W := mkw 0x4b789f70f7e2ef42 0x84b789f70f7e2ef4 0xfff83ff1ffc0ff0b 0xffff83ff1ffc0ff0

def z509 : W := mkw 0x9fbffdbcbbfe0000 0x19fbffdbcbbfe000 0xdffff9b03fff0007 0xfdffff9b03fff000

def z510 : W := mkw 0x0b3005003680a000 0x00b3005003680a00 0xfff807803fc0f00b 0xffff807803fc0f00

def z511 : W := mkw 0x0060024362004c53 0x00060024362004c5 0xb1e0064fe300ccfa 0xeb1e0064fe300ccf

def z512 : W := mkw 0x420005200400a200 0x0420005200400a20 0x000001b000003300 0x0000001b00000330

def z513 : W := mkw 0x1fdff7ff80431188 0x91fdff7ff8043118 0x5fffffffc0c7330f 0xd5fffffffc0c7330

def z514 : W := mkw 0x00e26acb63295cdb 0x000e26acb63295cd 0xf1e7ffcfe33ffcff 0xef1e7ffcfe33ffcf

def z515 : W := mkw 0x1f9ff5bc80000000 0x11f9ff5bc8000000 0x1ffff9b000000007 0xd1ffff9b00000000

def z516 : W := mkw 0x00c22a4341280453 0x000c22a434128045 0x11e63e4fc03800fe 0xc11e63e4fc03800f

def z517 : W := mkw 0x264547ff8c15b0ac 0x1264547ff8c15b0a 0xee07c7fffc3ff0fd 0xfee07c7fffc3ff0f

def z518 : W := mkw 0x2000408c000110ac 0x02000408c000110a 0x0000000e000000f0 0x00000000e000000f

def z519 : W := mkw 0x26054d8c4d35b4ee 0x026054d8c4d35b4e 0xee07ffcfff3ffcff 0xfee07ffcfff3ffcf

def z520 : W := mkw 0x00eafadbe36b5ddb 0x800eafadbe36b5dd 0xb1e7fe4fe33fccfe 0xeb1e7fe4fe33fccf

def z521 : W := mkw 0x26a76d8c2f3db0ac 0x026a76d8c2f3db0a 0xffe7ff8e3f3ff0ff 0xfffe7ff8e3f3ff0f

def z522 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x4019f809c3e700c7 0x64019f809c3e700c

def z523 : W := mkw 0x26e767cf2e1df8bd 0x026e767cf2e1df8b 0xffe7c78e3c3ff0fd 0xfffe7c78e3c3ff0f

def z524 : W := mkw 0x00089810c1620542 0x800089810c162054 0x20183879c3e00fce 0x620183879c3e00fc

def z525 : W := mkw 0x264547cf4c15fcff 0x0264547cf4c15fcf 0xee07c7cffc3ffcfd 0xfee07c7cffc3ffcf

def z526 : W := mkw 0x9fbffd8c3bfe0000 0x09fbffd8c3bfe000 0xdfffff8e3fff000f 0xfdfffff8e3fff000

def z527 : W := mkw 0x802000003a9c0000 0x0802000003a9c000 0x800000003c180000 0x0800000003c18000

def z528 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee01c1803c3ff0f1 0x3ee01c1803c3ff0f

def z529 : W := mkw 0x00004888416315ca 0x800004888416315c 0x6001c18803e73fcd 0x66001c18803e73fc

def z530 : W := mkw 0x0040024340004c53 0x00040024340004c5 0xa006064fe038ccfc 0xea006064fe038ccf

def z531 : W := mkw 0x4248dff8c563ffca 0x84248dff8c563ffc 0x6019fff9c3e7ffcf 0x66019fff9c3e7ffc

def z532 : W := mkw 0x402000003680ea00 0x0402000003680ea0 0xe01801f03fc0ff0b 0x6e01801f03fc0ff0

def z533 : W := mkw 0x00e2224362084c53 0x000e2224362084c5 0xb1e6064fe018ccf8 0x8b1e6064fe018ccf

def z534 : W := mkw 0x20e22a436f3dfcff 0x020e22a436f3dfcf 0xf1e63e4fff3ffcfe 0xef1e63e4fff3ffcf

def z535 : W := mkw 0x9dbfb80033ea0000 0x09dbfb80033ea000 0x1ffff80003c00007 0xd1ffff80003c0000

def z536 : W := mkw 0x2405408c0c15b0ac 0x02405408c0c15b0a 0xe007c00e3c3ff0f4 0x2e007c00e3c3ff0f

def z537 : W := mkw 0x1ffff7ffb2800000 0x11ffff7ffb280000 0xdfffffffffc0000f 0xfdfffffffffc0000

def z538 : W := mkw 0x1ff72f6763284c53 0x11ff72f6763284c5 0xbfe63e4fe338ccfe 0xfbfe63e4fe338ccf

def z539 : W := mkw 0x00089810c1620542 0x800089810c162054 0x00003801c0000000 0x000003801c000000

def z540 : W := mkw 0x1dbfb80023280000 0x01dbfb8002328000 0x9ffff80023380007 0xf9ffff8002338000

def z541 : W := mkw 0x00004098c00115ca 0x800004098c00115c 0x601801f9c3c03fcb 0x6601801f9c3c03fc

def z542 : W := mkw 0x00000800416315ca 0x800000800416315c 0x00000000002700c0 0x000000000002700c

def z543 : W := mkw 0x4b5007601480a200 0x04b5007601480a20 0x5ff807f01cc0330b 0xd5ff807f01cc0330

def z544 : W := mkw 0x0405000008140000 0x0040500000814000 0x0007c000003f0004 0x00007c000003f000

def z545 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018000003c00003 0x64018000003c0000

def z546 : W := mkw 0x0008d89881620000 0x00008d8988162000 0x4019f9f9c3e7000f 0x64019f9f9c3e7000

def z547 : W := mkw 0x94872000081c0000 0x094872000081c000 0x0006000000180000 0x0000600000018000

def z548 : W := mkw 0x02e26fffe3284c53 0x102e26fffe3284c5 0xb1e63fffe338ccfe 0xeb1e63fffe338ccf

def z549 : W := mkw 0x1fdfffffc1280453 0x11fdfffffc128045 0x1fffffffc03800ff 0xd1fffffffc03800f

def z550 : W := mkw 0x00004898c12115ca 0x800004898c12115c 0x200039f9c3203fce 0x6200039f9c3203fc

def z551 : W := mkw 0x424007600400ea00 0x0424007600400ea0 0xee0007f03c00ff09 0xfee0007f03c00ff0

def z552 : W := mkw 0xbdbfb8003fffb0ac 0x0bdbfb8003fffb0a 0xfffff8003ffff0f7 0xffffff8003ffff0f

def z553 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x6001f809c3e73fc4 0x26001f809c3e73fc

def z554 : W := mkw 0x0000080001200000 0x0000008000120000 0x0000380003200006 0x6000038000320000

def z555 : W := mkw 0x4b1005201480a200 0x04b1005201480a20 0x6e1801f01fc03f0b 0x76e1801f01fc03f0

def z556 : W := mkw 0x00aaf898e36b15ca 0x800aaf898e36b15c 0xf1fff9f9e3ff3fcf 0xef1fff9f9e3ff3fc

def z557 : W := mkw 0x4b78d7f8b6c3fb88 0x84b78d7f8b6c3fb8 0xfff9c7f03fc7ff0b 0xffff9c7f03fc7ff0

def z558 : W := mkw 0x0000408800011088 0x0000040880001108 0xe007c78e203ff0fd 0xee007c78e203ff0f

def z559 : W := mkw 0xdf1d95201cd6a200 0x0df1d95201cd6a20 0x4e19c1b01cc73301 0x14e19c1b01cc7330

def z560 : W := mkw 0x260dd59c8c57b1ac 0x8260dd59c8c57b1a 0x4e19c1b01cc73301 0x14e19c1b01cc7330

def z561 : W := mkw 0x6f7507643e94ea24 0x06f7507643e94ea2 0xfffe07f63fd8ff3b 0xffffe07f63fd8ff3

def z562 : W := mkw 0x00e26adbe3295ddb 0x800e26adbe3295dd 0xb1e63fffe338fffe 0xeb1e63fffe338fff

def z563 : W := mkw 0x1fdfb76700000000 0x11fdfb7670000000 0x1ffffe0600000007 0xd1ffffe060000000

def z564 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xbfe006403f00cc0a 0xfbfe006403f00cc0

def z565 : W := mkw 0x0b50076000000000 0x00b5007600000000 0x7ff807f003c03f0b 0xf7ff807f003c03f0

def z566 : W := mkw 0x0000408800000000 0x0000040880000000 0x0001c1880000000d 0x40001c1880000000

def z567 : W := mkw 0x9dbfb8007bff15ca 0x89dbfb8007bff15c 0xfffff8003fff3fc7 0xffffff8003fff3fc

def z568 : W := mkw 0x4b70076032804a00 0x04b70076032804a0 0x1ff807f003c00f0b 0xd1ff807f003c00f0

def z569 : W := mkw 0x1dffba4363284c53 0x01dffba4363284c5 0xbffffe4fe338ccff 0xfbffffe4fe338ccf

def z570 : W := mkw 0x948fb800097e0000 0x0948fb800097e000 0xce07f8003c3f0005 0xfce07f8003c3f000

def z571 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x201839f9c3c03fca 0x0201839f9c3c03fc

def z572 : W := mkw 0x0b50076000000000 0x00b5007600000000 0x1fe0060000000000 0x91fe006000000000

def z573 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xffe007803c00f009 0xfffe007803c00f00

def z574 : W := mkw 0x0008980001620000 0x0000898000162000 0x0018380003c00002 0x00018380003c0000

def z575 : W := mkw 0x1d9ff09880000000 0x01d9ff0988000000 0x1ffff9f9c000000f 0xd1ffff9f9c000000

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000003c03f00 0x26000000003c03f0

def z577 : W := mkw 0x602000003e95faac 0x0602000003e95faa 0xe00000003ffffff0 0x2e00000003ffffff

def z578 : W := mkw 0x0008d09880431188 0x80008d0988043118 0x6019c1b800e733cd 0x66019c1b800e733c

def z579 : W := mkw 0x9dbff898bbfe0000 0x09dbff898bbfe000 0xdffff9f9ffff000f 0xfdffff9f9ffff000

def z580 : W := mkw 0x9d1dd09898d71188 0x89d1dd09898d7118 0x4e19c1b01cc73301 0x14e19c1b01cc7330

def z581 : W := mkw 0x424007634400ee53 0x0424007634400ee5 0x200007ffc000fff8 0x0200007ffc000fff

def z582 : W := mkw 0x19daba73c1620542 0x919daba73c162054 0x11f83871c3c00f02 0x011f83871c3c00f0

def z583 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xbfe007f03c00ff08 0x9bfe007f03c00ff0

def z584 : W := mkw 0x00a2280023280000 0x000a228002328000 0x11e0380003000002 0x011e038000300000

def z585 : W := mkw 0xdbfabf6037eaea00 0x0dbfabf6037eaea0 0xfff83ff03fc0ff0b 0xffff83ff03fc0ff0

def z586 : W := mkw 0x0008d898c1200442 0x00008d898c120044 0x2019f9f9c3200ccf 0x62019f9f9c3200cc

def z587 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa006060e2338ccfc 0xea006060e2338ccf

def z588 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1e03e41e300cc0a 0xeb1e03e41e300cc0

def z589 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x31e03849c3200cce 0x631e03849c3200cc

def z590 : W := mkw 0x2605458c081510ac 0x02605458c081510a 0x0e07c78e003f00fd 0xd0e07c78e003f00f

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000008002000cc 0x620000008002000c

def z592 : W := mkw 0x00e2224322084811 0x000e222432208481 0x91e63e4fe018c03e 0xc91e63e4fe018c03

def z593 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa0003849e338ccfe 0x6a0003849e338ccf

def z594 : W := mkw 0x0020000022004800 0x0002000002200480 0xa00000002300cc00 0x2a00000002300cc0

def z595 : W := mkw 0x0068dad8e3635dca 0x80068dad8e3635dc 0xf1f9fff9e3e7ffcf 0xef1f9fff9e3e7ffc

def z596 : W := mkw 0xffffffec3ffffaac 0x0ffffffec3ffffaa 0xfffffffe3fffffff 0xffffffffe3ffffff

def z597 : W := mkw 0x0082200000000000 0x0008220000000000 0x11e6380000000006 0xc11e638000000000

def z598 : W := mkw 0x266547cc2e15f8ac 0x0266547cc2e15f8a 0xffe7c7ce3f3ffcff 0xfffe7c7ce3f3ffcf

def z599 : W := mkw 0x6f1545ac1c95b2ac 0x06f1545ac1c95b2a 0x4e19c1b01cc73301 0x14e19c1b01cc7330

def z600 : W := mkw 0x1f5dd7ff80000000 0x11f5dd7ff8000000 0x0e19c7ffc0000009 0x10e19c7ffc000000

def z601 : W := mkw 0x0b5047ff80000000 0x10b5047ff8000000 0x1ff807ffc000000b 0xd1ff807ffc000000

def z602 : W := mkw 0xbfbffd9cffffb5ee 0x8bfbffd9cffffb5e 0xffffffffffffffff 0xffffffffffffffff

def z603 : W := mkw 0x0082280001280000 0x0008228000128000 0x0006380000380004 0x0000638000038000

def z604 : W := mkw 0x4f7507603e94ea00 0x04f7507603e94ea0 0xffffc7f03fffff0f 0xfffffc7f03fffff0

def z605 : W := mkw 0x148ff89fc1280453 0x1148ff89fc128045 0x0007f80fc03800f4 0x00007f80fc03800f

def z606 : W := mkw 0x260505040c14a024 0x0260505040c14a02 0xee0607863c18f039 0xfee0607863c18f03

def z607 : W := mkw 0x0020080023280000 0x0002008002328000 0x8000000023380000 0x2800000002338000

def z608 : W := mkw 0x00600a4063284c53 0x000600a4063284c5 0xb1e006402338ccfa 0xeb1e006402338ccf

def z609 : W := mkw 0xdffffff8ffffffca 0x8dffffff8ffffffc 0xfffffff9ffffffcf 0xffffffff9ffffffc

def z610 : W := mkw 0x0b10052000000000 0x00b1005200000000 0x0e1801b000000001 0x10e1801b00000000

def z611 : W := mkw 0x00a2280363284c53 0x000a2280363284c5 0xa006380fe338ccf4 0x2a006380fe338ccf

def z612 : W := mkw 0x5fffb7603680ea00 0x05fffb7603680ea0 0xfffffff03fc0ff0f 0xffffffff03fc0ff0

def z613 : W := mkw 0x20000000081510ac 0x020000000081510a 0x00000000003f00f0 0x000000000003f00f

def z614 : W := mkw 0xdfffffffbffeea00 0x1dfffffffbffeea0 0xffffffffffffff0f 0xfffffffffffffff0

def z615 : W := mkw 0x22e26fcf6729fcff 0x022e26fcf6729fcf 0xb1e63fcfe338fcfe 0xeb1e63fcfe338fcf

def z616 : W := mkw 0x00caf2db80000000 0x000caf2db8000000 0x11ffffffc000000f 0xc11ffffffc000000

def z617 : W := mkw 0x5ff727673680ea00 0x15ff727673680ea0 0xfffe07f63fc0ff0b 0xffffe07f63fc0ff0

def z618 : W := mkw 0x4b1005201480a200 0x04b1005201480a20 0xee1807b03cc0f309 0xfee1807b03cc0f30

def z619 : W := mkw 0x4970026032804a00 0x04970026032804a0 0xb1f8067023c0cf0a 0xeb1f8067023c0cf0

def z620 : W := mkw 0x0405408c00000000 0x00405408c0000000 0x0007c00e00000004 0x00007c00e0000000

def z621 : W := mkw 0x2200458c0401b0ac 0x02200458c0401b0a 0x0000018000003000 0x0000001800000300

def z622 : W := mkw 0x4b3005203680a200 0x04b3005203680a20 0xdff801b03fc03303 0xfdff801b03fc0330

def z623 : W := mkw 0x020005000400a000 0x0020005000400a00 0x200007800000f008 0x0200007800000f00

def z624 : W := mkw 0x4b700f6077a0ee42 0x04b700f6077a0ee4 0xfff83ff9ffe0ffcf 0xffff83ff9ffe0ffc

def z625 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1e606062338ccf0 0xab1e606062338ccf

def z626 : W := mkw 0x406002403680ea00 0x0406002403680ea0 0xf1e006403fc0ff0a 0xef1e006403fc0ff0

def z627 : W := mkw 0x424047ff8400ea00 0x1424047ff8400ea0 0x200007ffc000ff08 0x0200007ffc000ff0

def z628 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1e03841e338ccf2 0x2b1e03841e338ccf

def z629 : W := mkw 0x6b7047ec3681faac 0x06b7047ec3681faa 0xfff807fe3fc0fffb 0xffff807fe3fc0fff

def z630 : W := mkw 0x0082200300080011 0x0008220030008001 0x0006000600180030 0x0000600060018003

def z631 : W := mkw 0x2405408c081510ac 0x02405408c081510a 0xce07c00e3c3f00f5 0xfce07c00e3c3f00f

def z632 : W := mkw 0x00089810c1620542 0x800089810c162054 0x601839f1c3c03f0b 0x6601839f1c3c03f0

def z633 : W := mkw 0x0000408800011088 0x0000040880001108 0x20000188000030c8 0x020000188000030c

def z634 : W := mkw 0x00000800416315ca 0x800000800416315c 0x601801f003e73fcb 0x6601801f003e73fc

def z635 : W := mkw 0x0000000000431188 0x8000000000043118 0x4000000000c73300 0x04000000000c7330

def z636 : W := mkw 0x94afb8002b7e0000 0x094afb8002b7e000 0x91e7f800233f0006 0xe91e7f800233f000

def z637 : W := mkw 0xbfbfbd043ffea024 0x0bfbfbd043ffea02 0xdffffe063fffc037 0xfdffffe063fffc03

def z638 : W := mkw 0x0405000008140000 0x0040500000814000 0x4e01c0001c070001 0x14e01c0001c07000

def z639 : W := mkw 0x4b5007600400ea00 0x04b5007600400ea0 0x3ff807f00000ff0b 0xd3ff807f00000ff0

def z640 : W := mkw 0x9db728003bfe0000 0x09db728003bfe000 0xdfe600003fff0000 0xbdfe600003fff000

def z641 : W := mkw 0x1fdfffffc1620542 0x91fdfffffc162054 0x1fffffffc3c00f0f 0xd1fffffffc3c00f0

def z642 : W := mkw 0x260ddd9ccd77b5ee 0x8260ddd9ccd77b5e 0xee07ff8ffc3ff0fd 0xfee07ff8ffc3ff0f

def z643 : W := mkw 0x0000409f80000000 0x10000409f8000000 0x0000000fc0000000 0x00000000fc000000

def z644 : W := mkw 0x0605050400000000 0x0060505040000000 0x0e06060600000000 0x90e0606060000000

def z645 : W := mkw 0x19faba73e3284c53 0x119faba73e3284c5 0x11f83871c3000c02 0x011f83871c3000c0

def z646 : W := mkw 0x00089810c16315ca 0x800089810c16315c 0x60183871c3e73fc2 0x260183871c3e73fc

def z647 : W := mkw 0x240dd89cc97715ee 0x8240dd89cc97715e 0x601ff9ffc3ff3fff 0x6601ff9ffc3ff3ff

def z648 : W := mkw 0x99b2200032880000 0x099b220003288000 0x11e0000000000000 0x011e000000000000

def z649 : W := mkw 0x0000080041200442 0x0000008004120044 0x601839f9c3e03fcf 0x6601839f9c3e03fc

def z650 : W := mkw 0x004042dbc0015ddb 0x8004042dbc0015dd 0x200007ffc000fff8 0x0200007ffc000fff

def z651 : W := mkw 0x240dd89cc97715ee 0x8240dd89cc97715e 0x0007f80fc03f00f4 0x00007f80fc03f00f

def z652 : W := mkw 0x00eaba43636a4c53 0x000eaba43636a4c5 0xf1fffe4fe3ffccff 0xef1fffe4fe3ffccf

def z653 : W := mkw 0xbf1dd58c1cd7b0ac 0x0bf1dd58c1cd7b0a 0xee1fc78e3cfff0fd 0xfee1fc78e3cfff0f

def z654 : W := mkw 0x0008d898c1620542 0x80008d898c162054 0x0019f9f9c3c00f0f 0x40019f9f9c3c00f0

def z655 : W := mkw 0x4b7047e83681fa88 0x04b7047e83681fa8 0xfff9c7f83fe7ffcf 0xffff9c7f83fe7ffc

def z656 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0x4e07c78e1c07300d 0xd4e07c78e1c07300

def z657 : W := mkw 0x1fffffffa3280000 0x11fffffffa328000 0x9fffffffe338000f 0xf9fffffffe338000

def z658 : W := mkw 0x16cff7ff80000000 0x116cff7ff8000000 0x0007ffffc000000c 0x00007ffffc000000

def z659 : W := mkw 0x0040024300004811 0x0004002430000481 0x000006060000c030 0x0000006060000c03

def z660 : W := mkw 0x6f7ddffcfff7ffee 0x86f7ddffcfff7ffe 0xffffffffffffffff 0xffffffffffffffff

def z661 : W := mkw 0x908ab800016a0000 0x0908ab800016a000 0x0000380000000000 0x0000038000000000

def z662 : W := mkw 0x0000080041200442 0x0000008004120044 0xa0063e4fe338ccfe 0xea0063e4fe338ccf

def z663 : W := mkw 0x2405408c081510ac 0x02405408c081510a 0xa007c60e203fc0fc 0xea007c60e203fc0f

def z664 : W := mkw 0x9dbfb810fbfe0542 0x89dbfb810fbfe054 0xdffff871ffff0f07 0xfdffff871ffff0f0

def z665 : W := mkw 0x00000010c0000542 0x800000010c000054 0x00000071c0000f00 0x000000071c0000f0

def z666 : W := mkw 0x424007600400ea00 0x0424007600400ea0 0x000006000000c000 0x0000006000000c00

def z667 : W := mkw 0x99bab80033ea0000 0x099bab80033ea000 0x91fe380023f80006 0xe91fe380023f8000

def z668 : W := mkw 0x00a2280363280453 0x000a228036328045 0x91e6380fe33800f6 0xe91e6380fe33800f

def z669 : W := mkw 0x00000000400115ca 0x800000000400115c 0x2000000000003fc0 0x02000000000003fc

def z670 : W := mkw 0x1d97200000000000 0x01d9720000000000 0x1fe6000000000000 0x91fe600000000000

def z671 : W := mkw 0x4028d898f7e3ffca 0x84028d898f7e3ffc 0xe019f9f9ffe7ffcf 0x6e019f9f9ffe7ffc

def z672 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x6001f989c02730cd 0x66001f989c02730c

def z673 : W := mkw 0x00e22a4323284811 0x000e22a432328481 0x91e63e062338c036 0xe91e63e062338c03

def z674 : W := mkw 0x4b700f6077e3ffca 0x84b700f6077e3ffc 0xfff807f03fe7ffcb 0xffff807f03fe7ffc

def z675 : W := mkw 0x0008980001620000 0x0000898000162000 0x0001f80000270004 0x00001f8000027000

def z676 : W := mkw 0x020045880401b088 0x0020045880401b08 0xee01c7883c27f0cd 0xfee01c7883c27f0c

def z677 : W := mkw 0x0000000340000453 0x0000000034000045 0x0000000fc00000f0 0x00000000fc00000f

def z678 : W := mkw 0x2605458c0401b0ac 0x02605458c0401b0a 0x2e07c78e0000f0fd 0xd2e07c78e0000f0f

def z679 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x0019f879c3e70fc6 0x00019f879c3e70fc

def z680 : W := mkw 0x9fffbf603bfe0000 0x09fffbf603bfe000 0xdffffff03fff000f 0xfdffffff03fff000

def z681 : W := mkw 0x0405408808151088 0x0040540880815108 0xee07c1883c3f30cd 0xfee07c1883c3f30c

def z682 : W := mkw 0x426007602600ea00 0x0426007602600ea0 0xb1e007f02300ff0a 0xeb1e007f02300ff0

def z683 : W := mkw 0x9dfffadbfbff5ddb 0x89dfffadbfbff5dd 0xffffffffffffffff 0xffffffffffffffff

def z684 : W := mkw 0x199ab00000000000 0x0199ab0000000000 0x11f8380000000002 0x011f838000000000

def z685 : W := mkw 0x9d9fb800097e0000 0x09d9fb800097e000 0x1ffff800003f0007 0xd1ffff800003f000

def z686 : W := mkw 0x9ff727673a9c0000 0x19ff727673a9c000 0x9fe606063c180000 0x99fe606063c18000

def z687 : W := mkw 0x1fffffffe36b5ddb 0x91fffffffe36b5dd 0xffffffffe3ffffff 0xfffffffffe3fffff

def z688 : W := mkw 0x0000408800011088 0x0000040880001108 0x4001c18000073001 0x04001c1800007300

def z689 : W := mkw 0x1fdfffffc16315ca 0x91fdfffffc16315c 0x1fffffffc02700cf 0xd1fffffffc02700c

def z690 : W := mkw 0xddffba603bfe4a00 0x0ddffba603bfe4a0 0xdffff8703fff0f07 0xfdffff8703fff0f0

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000018000003009 0x6600001800000300

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x200001f000003f08 0x0200001f000003f0

def z693 : W := mkw 0x80a228003bfe0000 0x080a228003bfe000 0xd1e638003fff0006 0xed1e638003fff000

def z694 : W := mkw 0x4bf227633688ea11 0x04bf227633688ea1 0x9fe606063c18c030 0x99fe606063c18c03

def z695 : W := mkw 0x948ff89f897e0000 0x1948ff89f897e000 0x0007f80fc03f0004 0x00007f80fc03f000

def z696 : W := mkw 0x00eaba53e36a4d53 0x800eaba53e36a4d5 0xb1fe3e7fe3f8cffe 0xeb1fe3e7fe3f8cff

def z697 : W := mkw 0x200000000c15b0ac 0x0200000000c15b0a 0x400000001c073000 0x0400000001c07300

def z698 : W := mkw 0x200000000401b0ac 0x0200000000401b0a 0x200000000000f0f0 0x0200000000000f0f

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018007003c00f02 0x00018007003c00f0

def z700 : W := mkw 0x0000000000000000 0x0000000000000000 0x8006000020380004 0xe800600002038000

def z701 : W := mkw 0x0008d88801631088 0x00008d8880163108 0x6019f98803e730cf 0x66019f98803e730c

def z702 : W := mkw 0x00eaba53e36a4d53 0x800eaba53e36a4d5 0x11f83871c3c00f02 0x011f83871c3c00f0

def z703 : W := mkw 0x0200050000000000 0x0020005000000000 0x0e00078000000009 0xd0e0007800000000

def z704 : W := mkw 0x9f1dd5bc98d60000 0x19f1dd5bc98d6000 0x4e19c1b01cc70001 0x14e19c1b01cc7000

def z705 : W := mkw 0x14effadfe3284c53 0x114effadfe3284c5 0xb1e7fe4fe338ccfe 0xeb1e7fe4fe338ccf

def z706 : W := mkw 0x060505000c14a000 0x0060505000c14a00 0xee07c7803c3ff00d 0xfee07c7803c3ff00

def z707 : W := mkw 0x5bdab7739480a200 0x15bdab7739480a20 0x5ff839f1dcc03303 0x15ff839f1dcc0330

def z708 : W := mkw 0x9dbfb8007bfe4c53 0x09dbfb8007bfe4c5 0xdffff8003fff0c07 0xfdffff8003fff0c0

def z709 : W := mkw 0xddbfb8003bfe4a00 0x0ddbfb8003bfe4a0 0xdffff8003fff0f07 0xfdffff8003fff0f0

def z710 : W := mkw 0x3fdff7ff8c57b1ac 0x93fdff7ff8c57b1a 0xfffffffffcfff3ff 0xffffffffffcfff3f

def z711 : W := mkw 0x26e76fcf6f3dfcff 0x026e76fcf6f3dfcf 0x5fe1f9c1df073c03 0x15fe1f9c1df073c0

def z712 : W := mkw 0x3fdff7ff8401b0ac 0x13fdff7ff8401b0a 0x1fffffffc000300f 0xd1fffffffc000300

def z713 : W := mkw 0x6d7542ec3a955aac 0x06d7542ec3a955aa 0x11ffc07e03ff0ff6 0x011ffc07e03ff0ff

def z714 : W := mkw 0x1dd7224300000000 0x01dd722430000000 0x1fe63e4fc000000e 0xd1fe63e4fc000000

def z715 : W := mkw 0x54aff09fb680ea00 0x154aff09fb680ea0 0xe007f80fffc0ff04 0x2e007f80fffc0ff0

def z716 : W := mkw 0x0f5dd7fc80000000 0x00f5dd7fc8000000 0x1fffffffc000000f 0xd1fffffffc000000

def z717 : W := mkw 0x948ff89bc97f15db 0x8948ff89bc97f15d 0x0007f80fc03f00f4 0x00007f80fc03f00f

def z718 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0x7ff801f01fc03f0b 0x77ff801f01fc03f0

def z719 : W := mkw 0x04c762cf00000000 0x004c762cf0000000 0x11e7fe4fc000000e 0xc11e7fe4fc000000

def z720 : W := mkw 0x260d9d14cd76a566 0x8260d9d14cd76a56 0x8e1e3e77ffd8cf32 0x98e1e3e77ffd8cf3

def z721 : W := mkw 0x0028d898e36b5ddb 0x80028d898e36b5dd 0xe019c1b023fffff1 0x2e019c1b023fffff

def z722 : W := mkw 0x1bdab77780000000 0x11bdab7778000000 0x11f83e77c0000002 0x011f83e77c000000

def z723 : W := mkw 0x0082200300000000 0x0008220030000000 0x11e6380fc0000006 0xc11e6380fc000000

def z724 : W := mkw 0x19dab27380000000 0x119dab2738000000 0xb1fe3e7fe038c0fe 0xeb1fe3e7fe038c0f

def z725 : W := mkw 0x7fdff7ff9c95b2ac 0x17fdff7ff9c95b2a 0xfffffffffcfff3ff 0xffffffffffcfff3f

def z726 : W := mkw 0x9d9fb00018d60000 0x09d9fb00018d6000 0x5ff9f8001cc70003 0x15ff9f8001cc7000

def z727 : W := mkw 0x9db720003a9c0000 0x09db720003a9c000 0xdfffc0003fff0007 0xfdfffc0003fff000

def z728 : W := mkw 0x4b58d7f894c3b388 0x84b58d7f894c3b38 0x5ff9fff9dcc7330f 0xd5ff9fff9dcc7330

def z729 : W := mkw 0xd6cfbf600d7eea00 0x0d6cfbf600d7eea0 0x2007fff0003fff0c 0x02007fff0003fff0

def z730 : W := mkw 0x1fdff7ff80420100 0x91fdff7ff8042010 0x1fffffffc0c0030f 0xd1fffffffc0c0030

def z731 : W := mkw 0x1fdff7ff80420000 0x11fdff7ff8042000 0x5fffffffc0c7000f 0xd5fffffffc0c7000

def z732 : W := mkw 0x99faba73f3ea4c53 0x199faba73f3ea4c5 0x11f83871c3c00c02 0x011f83871c3c00c0

def z733 : W := mkw 0x5fdff7ff9480ea00 0x15fdff7ff9480ea0 0x7fffffffdcc0ff0f 0xd7fffffffdcc0ff0

def z734 : W := mkw 0x19dab24300000000 0x019dab2430000000 0x11f83841c0000002 0x011f83841c000000

def z735 : W := mkw 0x0b58d7f88401b088 0x00b58d7f88401b08 0xfff9fff9fc27f0cf 0xffff9fff9fc27f0c

def z736 : W := mkw 0x1d9ff09880000000 0x01d9ff0988000000 0x1ffff809c0000007 0xd1ffff809c000000

def z737 : W := mkw 0x4b3005203680ea00 0x04b3005203680ea0 0xfff801b03fc0ff03 0xffff801b03fc0ff0

def z738 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ff9fff1c000000b 0xd1ff9fff1c000000

def z739 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdfe7f8003fff0004 0xbdfe7f8003fff000

def z740 : W := mkw 0x9ddfb24318d60000 0x09ddfb24318d6000 0x5ffffe4fdcc7000f 0xd5ffffe4fdcc7000

def z741 : W := mkw 0x0fd767ef00000000 0x00fd767ef0000000 0x1fffffffc000000f 0xd1fffffffc000000

def z742 : W := mkw 0x1ddff2ff80000000 0x11ddff2ff8000000 0x11fffe7fc000000e 0xc11fffe7fc000000

def z743 : W := mkw 0x0bd2276300000000 0x00bd227630000000 0x1fe63e4fc000000e 0xd1fe63e4fc000000

def z744 : W := mkw 0x1fdff7ff8400a000 0x11fdff7ff8400a00 0x5fffffffdc00300f 0xd5fffffffdc00300

def z745 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0xdffffffffc1ff03f 0xddffffffffc1ff03

def z746 : W := mkw 0x1ddfb27380000000 0x11ddfb2738000000 0x1ffe3871c0000002 0x91ffe3871c000000

def z747 : W := mkw 0x9d3d90003ad60000 0x09d3d90003ad6000 0x5ff9c0001fc70003 0x15ff9c0001fc7000

def z748 : W := mkw 0xbbbafd8c37ebb0ac 0x0bbbafd8c37ebb0a 0x31f83f8e03c0f0fa 0x031f83f8e03c0f0f

def z749 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdff9f8003fff0003 0x3dff9f8003fff000

def z750 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x5ffff8001fc70007 0xd5ffff8001fc7000

def z751 : W := mkw 0x59dab27390800200 0x159dab2739080020 0x11f83871c0c00302 0x011f83871c0c0030

def z752 : W := mkw 0x9dbfb813bbfe0000 0x19dbfb813bbfe000 0xdffff801ffff0007 0xfdffff801ffff000

def z753 : W := mkw 0x0487200008140000 0x0048720000814000 0xdfe7f8003c3f0007 0xfdfe7f8003c3f000

def z754 : W := mkw 0x09d2226300000000 0x009d222630000000 0x11f83871c0000002 0x011f83871c000000

def z755 : W := mkw 0x9dbfb8007bfe4c53 0x09dbfb8007bfe4c5 0xfffff849ffffccff 0xffffff849ffffccf

def z756 : W := mkw 0x602008007ff7ffee 0x8602008007ff7ffe 0xe00000003ffffff0 0x2e00000003ffffff

def z757 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdff9f8003fc70003 0xfdff9f8003fc7000

def z758 : W := mkw 0x00089810c1620542 0x800089810c162054 0x6019f9f1c3e73f0f 0x66019f9f1c3e73f0

def z759 : W := mkw 0x3fd767ef0c15b0ac 0x13fd767ef0c15b0a 0xffe7ffcffc3ff0ff 0xfffe7ffcffc3ff0f

def z760 : W := mkw 0x00eaf2dba24b5999 0x800eaf2dba24b599 0xd1ffc7b620dff331 0x8d1ffc7b620dff33

def z761 : W := mkw 0x19d2226300000000 0x119d222630000000 0x11e63e4fc000000e 0xc11e63e4fc000000

def z762 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0xee19f9f9ffe73fcf 0xfee19f9f9ffe73fc

def z763 : W := mkw 0xbf1dd59c9cd7b1ac 0x8bf1dd59c9cd7b1a 0x4e19c1b01cc73301 0x14e19c1b01cc7330

def z764 : W := mkw 0x224047dfc401fdff 0x8224047dfc401fdf 0x200007ffc000fff8 0x0200007ffc000fff

def z765 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1e63e0fe338ccf4 0xab1e63e0fe338ccf

def z766 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfff83ff9ffc0ff0f 0xffff83ff9ffc0ff0

def z767 : W := mkw 0x4020080073a84e53 0x04020080073a84e5 0x0000000003c00f00 0x00000000003c00f0

def z768 : W := mkw 0x4b7007633680ea00 0x04b7007633680ea0 0xfff807ffffc0ff0b 0xffff807ffffc0ff0

def z769 : W := mkw 0x9d3d90003ad60000 0x09d3d90003ad6000 0xdfffc0003fff0007 0xfdfffc0003fff000

def z770 : W := mkw 0x82604fffbbfe0000 0x182604fffbbfe000 0xc00007ffffff0008 0x2c00007ffffff000

def z771 : W := mkw 0x1fdff7ff80011088 0x11fdff7ff8001108 0xffffffffe03ff0ff 0xfffffffffe03ff0f

def z772 : W := mkw 0x624047ef4401feff 0x0624047ef4401fef 0x200007ffc000fff8 0x0200007ffc000fff

def z773 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0x5fffffffdc3f30ff 0xd5fffffffdc3f30f

def z774 : W := mkw 0x4970026032804a00 0x04970026032804a0 0xfff801f03fc03f0b 0xffff801f03fc03f0

def z775 : W := mkw 0x5fdff7ff9480a200 0x15fdff7ff9480a20 0x1fffffffdc00000f 0xd1fffffffdc00000

def z776 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x5ff9f8001fe70007 0x75ff9f8001fe7000

def z777 : W := mkw 0x6f1dd5bc9cd7b3ac 0x86f1dd5bc9cd7b3a 0x4e19c1b01cc73301 0x14e19c1b01cc7330

def z778 : W := mkw 0x0008d89881620000 0x00008d8988162000 0x6019f9f9c3e73f0f 0x66019f9f9c3e73f0

def z779 : W := mkw 0x1f3dddbce3284c53 0x11f3dddbce3284c5 0xae19c1b02338ccf1 0x3ae19c1b02338ccf

def z780 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1fffffffc03800ff 0xd1fffffffc03800f

def z781 : W := mkw 0x9d9fb00018d60000 0x09d9fb00018d6000 0xdffff8003cff0007 0xfdffff8003cff000

def z782 : W := mkw 0x2f5dd7fc8c15b0ac 0x02f5dd7fc8c15b0a 0xfffffffffc3ff0ff 0xffffffffffc3ff0f

def z783 : W := mkw 0x202008006729fcff 0x0202008006729fcf 0xa00000002338fcf0 0x2a00000002338fcf

def z784 : W := mkw 0x00e22a4323280000 0x000e22a432328000 0xb1e63e4fe338c0fe 0xeb1e63e4fe338c0f

def z785 : W := mkw 0x802008007bfe0542 0x8802008007bfe054 0xc00000003fff0f00 0x2c00000003fff0f0

def z786 : W := mkw 0x00c2224300000000 0x000c222430000000 0x91e606062018c030 0x891e606062018c03

def z787 : W := mkw 0x4b922d2355a8a653 0x04b922d2355a8a65 0x4e1e39bfdcf833f5 0x14e1e39bfdcf833f

def z788 : W := mkw 0x1ddff2df80000000 0x11ddff2df8000000 0x1ffffe4fc000000f 0xd1ffffe4fc000000

def z789 : W := mkw 0x1d9fb00008140000 0x01d9fb0000814000 0x5ffff8001c070007 0xd5ffff8001c07000

def z790 : W := mkw 0x348ff89fc97715ee 0x9348ff89fc97715e 0x0007f80fc03f00f4 0x00007f80fc03f00f

def z791 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xfffff8003fff3f07 0xffffff8003fff3f0

def z792 : W := mkw 0x1fdfb77780000000 0x11fdfb7778000000 0x1ffffe77c0000007 0xd1ffffe77c000000

def z793 : W := mkw 0x4020080077ebffdb 0x84020080077ebffd 0xe00000003ffffff0 0x2e00000003ffffff

def z794 : W := mkw 0x3fdff7ff8400a024 0x13fdff7ff8400a02 0x1fffffffc000c03f 0xd1fffffffc000c03

def z795 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11f83871c3c00f02 0x011f83871c3c00f0

def z796 : W := mkw 0x4b78dff8f7e3ffca 0x84b78dff8f7e3ffc 0x9fe1fe09fc27c0c4 0x99fe1fe09fc27c0c

def z797 : W := mkw 0x1d9fb00300000000 0x01d9fb0030000000 0x1ffff80fc0000007 0xd1ffff80fc000000

def z798 : W := mkw 0x9d5d924358d64c53 0x09d5d924358d64c5 0x6e19c64fdcc7ccf9 0x16e19c64fdcc7ccf

def z799 : W := mkw 0x9dbfb0003ad60000 0x09dbfb0003ad6000 0xdffff8003fc70007 0xfdffff8003fc7000

def z800 : W := mkw 0x00600a4063284c53 0x000600a4063284c5 0xa00006402338ccf8 0x2a00006402338ccf

def z801 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffff9f03fff000f 0xfdffff9f03fff000

def z802 : W := mkw 0xa6254d8c7fffb5ee 0x8a6254d8c7fffb5e 0xee07c78e3ffffffd 0xfee07c78e3ffffff

def z803 : W := mkw 0x9dbfb8007bfe0453 0x09dbfb8007bfe045 0xdffff8003fff00f7 0xfdffff8003fff00f

def z804 : W := mkw 0x060505000c14a000 0x0060505000c14a00 0xee07c78e3c3ff0fd 0xfee07c78e3c3ff0f

def z805 : W := mkw 0x0082200000000000 0x0008220000000000 0x91e6380020380006 0xe91e638002038000

def z806 : W := mkw 0x7ff727673e94ea24 0x17ff727673e94ea2 0x9fe606063c18c030 0x99fe606063c18c03

def z807 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ffffff7c0000003 0x91ffffff7c000000

def z808 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfffe07f63fd8ff3b 0xffffe07f63fd8ff3

def z809 : W := mkw 0x16cff7ff80000000 0x116cff7ff8000000 0x11e7ffffc000000e 0xc11e7ffffc000000

def z810 : W := mkw 0x1fdff7ff88140000 0x11fdff7ff8814000 0x9ffffffffc18000f 0xd9ffffffffc18000

def z811 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x9fffffffe038000f 0xf9fffffffe038000

def z812 : W := mkw 0x40e22a4373a84e53 0x040e22a4373a84e5 0xb1e63e4fe3f8cffe 0xeb1e63e4fe3f8cff

def z813 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffff8003fdf0003 0x9dffff8003fdf000

def z814 : W := mkw 0x00c22a4341280453 0x000c22a434128045 0xb1e63e4fe038c0fe 0xeb1e63e4fe038c0f

def z815 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x7fffffffc000300f 0xf7fffffffc000300

def z816 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0x5ff9f9f1dc073003 0x15ff9f9f1dc07300

def z817 : W := mkw 0x2fd767ef0c15b0ac 0x02fd767ef0c15b0a 0xfffffffffc3ff0ff 0xffffffffffc3ff0f

def z818 : W := mkw 0x19daf2ff80000000 0x119daf2ff8000000 0x11f8387fc0000002 0x011f8387fc000000

def z819 : W := mkw 0x9db76098fa9d15ca 0x89db76098fa9d15c 0xbfe601f9fc183fc8 0x9bfe601f9fc183fc

def z820 : W := mkw 0x7fdff7ff8c15faac 0x17fdff7ff8c15faa 0xfffffffffc3fffff 0xffffffffffc3ffff

def z821 : W := mkw 0x9dbfb810bbfe0000 0x09dbfb810bbfe000 0xdffff871ffff0007 0xfdffff871ffff000

def z822 : W := mkw 0x8d3508003bfe0000 0x08d3508003bfe000 0xdfffc0003fff0007 0xfdfffc0003fff000

def z823 : W := mkw 0x00a2280063280442 0x000a228006328044 0xb1e63e4fe338ccfe 0xeb1e63e4fe338ccf

def z824 : W := mkw 0x1fd72f67416315ca 0x91fd72f67416315c 0x7fe6060603e73fc0 0xb7fe6060603e73fc

def z825 : W := mkw 0x0040024300000000 0x0004002430000000 0x2000064fc000c0f8 0x02000064fc000c0f

def z826 : W := mkw 0x0020080063284c53 0x00020080063284c5 0x0000000003380cf0 0x00000000003380cf

def z827 : W := mkw 0x9dbfb8037bfe0453 0x09dbfb8037bfe045 0xfffff84fffff0cff 0xffffff84fffff0cf

def z828 : W := mkw 0x9dbfb8033bfe0011 0x09dbfb8033bfe001 0xdffff8063fff0037 0xfdffff8063fff003

def z829 : W := mkw 0x0958927080000000 0x0095892708000000 0x11f83871c0000002 0x011f83871c000000

def z830 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e63e0fc0000004 0x811e63e0fc000000

def z831 : W := mkw 0x1fdff7ff8400a000 0x11fdff7ff8400a00 0xfffffffffc38f0ff 0xffffffffffc38f0f

def z832 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdfffc0003fff0001 0xbdfffc0003fff000

def z833 : W := mkw 0x424047fbc401ffdb 0x8424047fbc401ffd 0x200007ffc000fff8 0x0200007ffc000fff

def z834 : W := mkw 0x19dab27380420100 0x919dab2738042010 0x11f83871c0c00302 0x011f83871c0c0030

def z835 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x5fffffffc0c0330f 0xd5fffffffc0c0330

def z836 : W := mkw 0x4b3005203680a200 0x04b3005203680a20 0xfff801f03fc03f0b 0xffff801f03fc03f0

def z837 : W := mkw 0x224047ffc401b5ee 0x9224047ffc401b5e 0x200007ffc000fff8 0x0200007ffc000fff

def z838 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x9fe7f8003f3f0006 0xf9fe7f8003f3f000

def z839 : W := mkw 0x4028d098b680ea00 0x04028d098b680ea0 0xe019f9f9ffc0ff0f 0x6e019f9f9ffc0ff0

def z840 : W := mkw 0x1fdff7ff8400a000 0x11fdff7ff8400a00 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z841 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x5ffff8001fff0007 0x15ffff8001fff000

def z842 : W := mkw 0x1bdab77380000000 0x11bdab7738000000 0x11f83ff1c000000a 0x011f83ff1c000000

def z843 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x3fffffffc0003f0f 0xd3fffffffc0003f0

def z844 : W := mkw 0x59dab27380004a00 0x159dab27380004a0 0x11f83871c0000f02 0x011f83871c0000f0

def z845 : W := mkw 0x42200d0077a8ee53 0x042200d0077a8ee5 0xee06078e3ff8fffd 0xfee06078e3ff8fff

def z846 : W := mkw 0x22c267ff8401b0ac 0x122c267ff8401b0a 0xb1e63fffe038f0fe 0xeb1e63fffe038f0f

def z847 : W := mkw 0x1fdfb77780000000 0x11fdfb7778000000 0x1fe63e07c0000000 0x91fe63e07c000000

def z848 : W := mkw 0x0008d09880431188 0x80008d0988043118 0x6019f9f9c3c73f0f 0x66019f9f9c3c73f0

def z849 : W := mkw 0x14cfb24300000000 0x014cfb2430000000 0x11e7fe4fc000000e 0xc11e7fe4fc000000

def z850 : W := mkw 0x0020080063284c53 0x00020080063284c5 0x800000002038c0f0 0x0800000002038c0f

def z851 : W := mkw 0x3fdff7ff881510ac 0x13fdff7ff881510a 0xbfffffffe03fc0ff 0xfbfffffffe03fc0f

def z852 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11fe3871c0000006 0xc11fe3871c000000

def z853 : W := mkw 0x9dffba433bfe0000 0x09dffba433bfe000 0xfffffe4fffffc0ff 0xffffffe4fffffc0f

def z854 : W := mkw 0x224047cf0401b0ac 0x0224047cf0401b0a 0x200007cfc000f0f8 0x0200007cfc000f0f

def z855 : W := mkw 0x0605458c08140000 0x00605458c0814000 0xee07c78e3c3fc0fd 0xfee07c78e3c3fc0f

def z856 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0xdffffffffc00000f 0xfdffffffffc00000

def z857 : W := mkw 0x248ff89fc97f15ff 0x8248ff89fc97f15f 0x0007f80fc03f00f4 0x00007f80fc03f00f

def z858 : W := mkw 0x9dbfb8003bfe4811 0x09dbfb8003bfe481 0xdffff8003fffc037 0xfdffff8003fffc03

def z859 : W := mkw 0x42204d8877e3ffca 0x842204d8877e3ffc 0xee01c7883fe7ffcd 0xfee01c7883fe7ffc

def z860 : W := mkw 0x00c22a4341284c53 0x000c22a4341284c5 0x31e63e4fc038ccfe 0xc31e63e4fc038ccf

def z861 : W := mkw 0x00c2227380000000 0x100c222738000000 0x11e63e7fc000000e 0xc11e63e7fc000000

def z862 : W := mkw 0x1f9ff59c80000000 0x01f9ff59c8000000 0x1fffffffc000000f 0xd1fffffffc000000

def z863 : W := mkw 0x00c22a4341200442 0x000c22a434120044 0xb1e63e4fe338ccfe 0xeb1e63e4fe338ccf

def z864 : W := mkw 0x1fdff7ff88140000 0x11fdff7ff8814000 0x1fffffffc03f000f 0xd1fffffffc03f000

def z865 : W := mkw 0x9d9fb800097e0000 0x09d9fb800097e000 0xdffff8003c3f0007 0xfdffff8003c3f000

def z866 : W := mkw 0x16cff7df80000000 0x116cff7df8000000 0x1fe7ffcfc000000f 0xd1fe7ffcfc000000

def z867 : W := mkw 0x842508007bfe4c53 0x0842508007bfe4c5 0xee07c60e3fffccfd 0xfee07c60e3fffccf

def z868 : W := mkw 0x0445024348144c53 0x00445024348144c5 0xee07c64ffc3fccfd 0xfee07c64ffc3fccf

def z869 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfff807b03fc0ff01 0xbfff807b03fc0ff0

def z870 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e63e4fc03800fe 0xc11e63e4fc03800f

def z871 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xce07c78e3c3ff0f5 0x9ce07c78e3c3ff0f

def z872 : W := mkw 0x19daf2fb80431188 0x919daf2fb8043118 0x51f9f9f1c0c73303 0x051f9f9f1c0c7330

def z873 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0xfffffffffc07f00f 0xffffffffffc07f00

def z874 : W := mkw 0x00c2224300004800 0x000c222430000480 0x31e63e4fc000cc0e 0xc31e63e4fc000cc0

def z875 : W := mkw 0x893898003bfe0000 0x0893898003bfe000 0xdff9f8003fff0007 0xfdff9f8003fff000

def z876 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffff849ffff000f 0xfdffff849ffff000

def z877 : W := mkw 0x1fd7276700000000 0x11fd727670000000 0x1fe63e47c0000002 0x91fe63e47c000000

def z878 : W := mkw 0x10cab25380000000 0x110cab2538000000 0x11e03841c0000002 0x011e03841c000000

def z879 : W := mkw 0x4b3005203680ea00 0x04b3005203680ea0 0x4e1801b01fc03f01 0x14e1801b01fc03f0

def z880 : W := mkw 0x9dbfb0003ade0000 0x09dbfb0003ade000 0x5ff9c0001cc70001 0x15ff9c0001cc7000

def z881 : W := mkw 0x1f9ff59f80000000 0x11f9ff59f8000000 0x1fffff8fc000000f 0xd1fffff8fc000000

def z882 : W := mkw 0x9dbfb0003ade0000 0x09dbfb0003ade000 0xdffff8003cdf0007 0xddffff8003cdf000

def z883 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ff9ffffc000000b 0x11ff9ffffc000000

def z884 : W := mkw 0x1fdff7ff80004811 0x11fdff7ff8000481 0x1fffffffc000c03f 0xd1fffffffc000c03

def z885 : W := mkw 0x0008d898c16b15db 0x80008d898c16b15d 0x6019f9f9c3ff3fff 0x66019f9f9c3ff3ff

def z886 : W := mkw 0x0405408808151088 0x0040540880815108 0xee07c78e3c3ff0fd 0xfee07c78e3c3ff0f

def z887 : W := mkw 0x624047fcc401ffee 0x8624047fcc401ffe 0x200007ffc000fff8 0x0200007ffc000fff

def z888 : W := mkw 0x224047ef0401b0ac 0x1224047ef0401b0a 0x2000078e0000f0f8 0x02000078e0000f0f

def z889 : W := mkw 0x1bdaf7ff80000000 0x11bdaf7ff8000000 0x11f9ffffc000000f 0x411f9ffffc000000

def z890 : W := mkw 0x224047ffc401fcff 0x1224047ffc401fcf 0x200007ffc000fcf8 0x0200007ffc000fcf

def z891 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa00006002338ccf8 0xea00006002338ccf

def z892 : W := mkw 0x202008006f7ffdff 0x8202008006f7ffdf 0xe00000003ffffff0 0x2e00000003ffffff

def z893 : W := mkw 0x199ab01380000000 0x1199ab0138000000 0x11f83801c0000002 0x011f83801c000000

def z894 : W := mkw 0x1ddff2ff80000000 0x11ddff2ff8000000 0x1ffff87fc0000007 0xd1ffff87fc000000

def z895 : W := mkw 0x020045880401b088 0x0020045880401b08 0xee07c78e3c3ff0fd 0xfee07c78e3c3ff0f

def z896 : W := mkw 0x00c2224300004811 0x000c222430000481 0x11e63e4fc000c03e 0xc11e63e4fc000c03

def z897 : W := mkw 0x1bdab77380000000 0x11bdab7738000000 0x1ff839f1c0000003 0x11ff839f1c000000

def z898 : W := mkw 0x9dbfb830bbfe0000 0x19dbfb830bbfe000 0xdffff8303fff0007 0xfdffff8303fff000

def z899 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11fe387fc0000006 0x011fe387fc000000

def z900 : W := mkw 0x0008d09880011088 0x00008d0988001108 0x6019f9f9c3e73fcf 0x66019f9f9c3e73fc

def z901 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x601fffffc3e73fcf 0xe601fffffc3e73fc

def z902 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x3fffffffc000c0ff 0xd3fffffffc000c0f

def z903 : W := mkw 0x1fdff7ff88140000 0x11fdff7ff8814000 0x5fffffffdc07000f 0xd5fffffffdc07000

def z904 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x5fffffffc027000f 0xf5fffffffc027000

def z905 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0x7fffffffdc2730cf 0xf7fffffffdc2730c

def z906 : W := mkw 0x4020080077e2ef42 0x84020080077e2ef4 0xe00000003fc0ff00 0x2e00000003fc0ff0

def z907 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa000060e2338ccf8 0x2a000060e2338ccf

def z908 : W := mkw 0x9dbfb0003ade0000 0x09dbfb0003ade000 0xdfffc0003cff0005 0xfdfffc0003cff000

def z909 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xe000000023f8fff0 0x2e000000023f8fff

def z910 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0xffffffffffffffff 0xffffffffffffffff

def z911 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffffe0e3fff000f 0xfdffffe0e3fff000

def z912 : W := mkw 0x802008007bfe0453 0x0802008007bfe045 0xc00000003fff00f0 0x2c00000003fff00f

def z913 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa00000082338ccfc 0x6a00000082338ccf

def z914 : W := mkw 0x1ddff2fb80000000 0x11ddff2fb8000000 0x1ffff9f9c000000f 0xd1ffff9f9c000000

def z915 : W := mkw 0x5fdff7ff8400ea00 0x15fdff7ff8400ea0 0x1fffffffc000c00f 0xd1fffffffc000c00

def z916 : W := mkw 0x02200d006728ec53 0x002200d006728ec5 0xee0007803f38fcf9 0xfee0007803f38fcf

def z917 : W := mkw 0x3fdff7ff8c14a024 0x13fdff7ff8c14a02 0x1fffffffdc00000f 0xd1fffffffdc00000

def z918 : W := mkw 0x0938900032c20000 0x00938900032c2000 0xdff9c0003fc70003 0xfdff9c0003fc7000

def z919 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfff807f03ff8fffb 0xffff807f03ff8fff

def z920 : W := mkw 0x1dbfb8002b3c0000 0x01dbfb8002b3c000 0xdffff8003f3f0007 0xfdffff8003f3f000

def z921 : W := mkw 0x0b5007600400a000 0x00b5007600400a00 0xfff807f03fc0ff0b 0xffff807f03fc0ff0

def z922 : W := mkw 0xbdbfb8043bfe0024 0x0bdbfb8043bfe002 0xdffff8063fff0037 0xfdffff8063fff003

def z923 : W := mkw 0x1fdfb77380000000 0x11fdfb7738000000 0x1ffffff1c000000f 0xd1ffffff1c000000

def z924 : W := mkw 0x1fdff7ff80011088 0x11fdff7ff8001108 0x3fffffffc00030cf 0xd3fffffffc00030c

def z925 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfff801f03fc0ff03 0x3fff801f03fc0ff0

def z926 : W := mkw 0x0db728003bbc0000 0x00db728003bbc000 0xdffff8003fff0007 0xfdffff8003fff000

def z927 : W := mkw 0x1fdff7ff8400a000 0x11fdff7ff8400a00 0x3fffffffc000f00f 0xd3fffffffc000f00

def z928 : W := mkw 0x0020080073e315ca 0x80020080073e315c 0xe00000003fe73fc0 0x2e00000003fe73fc

def z929 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11f83879c000000e 0x411f83879c000000

def z930 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1fe7ffffc000000c 0x91fe7ffffc000000

def z931 : W := mkw 0x3fdff7ff881510ac 0x13fdff7ff881510a 0x7fffffffc03f30ff 0xf7fffffffc03f30f

def z932 : W := mkw 0x9d3d98003bf60000 0x09d3d98003bf6000 0xdff9f8003fe70007 0xfdff9f8003fe7000

def z933 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfffe07fe3fc0ff0f 0xffffe07fe3fc0ff0

def z934 : W := mkw 0x7fdff7ff8401faac 0x17fdff7ff8401faa 0x3fffffffc000ffff 0xd3fffffffc000fff

def z935 : W := mkw 0x802008007bff15ca 0x8802008007bff15c 0xc00000003fff00c0 0x2c00000003fff00c

def z936 : W := mkw 0x9d1d900018d60000 0x09d1d900018d6000 0x5ff9c0001cc70003 0xd5ff9c0001cc7000

def z937 : W := mkw 0x002008006728ec53 0x0002008006728ec5 0xe00000003f38fcf0 0x2e00000003f38fcf

def z938 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x4019f9f9c3e73fc7 0x04019f9f9c3e73fc

def z939 : W := mkw 0x04a720002a1c0000 0x004a720002a1c000 0xdfe7c0003c3f0005 0xfdfe7c0003c3f000

def z940 : W := mkw 0x3fdff7ff88140024 0x13fdff7ff8814002 0x1fffffffc018003f 0xd1fffffffc018003

def z941 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee07ffcffc3ff0ff 0xfee07ffcffc3ff0f

def z942 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xfffff8003fffc0f7 0xffffff8003fffc0f

def z943 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x4019f9f9c3c73f0f 0x44019f9f9c3c73f0

def z944 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0xbfffffffe000c00f 0xfbfffffffe000c00

def z945 : W := mkw 0x8020080073eb15ca 0x88020080073eb15c 0x6000000003e73fc0 0x26000000003e73fc

def z946 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e03e41c000000a 0xc11e03e41c000000

def z947 : W := mkw 0x3ddff2ff881510ac 0x13ddff2ff881510a 0x11fff87fc03f00f6 0x011fff87fc03f00f

def z948 : W := mkw 0x19daf2fb80000000 0x119daf2fb8000000 0x11f839f9c000000a 0x011f839f9c000000

def z949 : W := mkw 0x3fdff7ff800110ac 0x13fdff7ff800110a 0x1fffffffc00000ff 0xd1fffffffc00000f

def z950 : W := mkw 0x1fdfb77780000000 0x11fdfb7778000000 0x1ff83871c0000002 0x11ff83871c000000

def z951 : W := mkw 0x00200800636a4c53 0x000200800636a4c5 0xe000000023ffccf0 0x2e000000023ffccf

def z952 : W := mkw 0x0d3500003a940000 0x00d3500003a94000 0xdfe7c0003c3f0005 0xfdfe7c0003c3f000

def z953 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0xe019f9f9e3ffffff 0x6e019f9f9e3fffff

def z954 : W := mkw 0x9dbfb0003ade0000 0x09dbfb0003ade000 0x9fe7c0003c1f0000 0x99fe7c0003c1f000

def z955 : W := mkw 0x9d9fb80019f60000 0x09d9fb80019f6000 0x5ffff8001fe70007 0xf5ffff8001fe7000

def z956 : W := mkw 0x1d9fb01080000000 0x01d9fb0108000000 0x1ffff871c0000007 0xd1ffff871c000000

def z957 : W := mkw 0x224047ff8401b0ac 0x1224047ff8401b0a 0x000007ffc0003008 0x0000007ffc000300

def z958 : W := mkw 0x1fdff7ff90800000 0x11fdff7ff9080000 0x5fffffffdcc0000f 0xd5fffffffdcc0000

def z959 : W := mkw 0x202008006b3d5cff 0x0202008006b3d5cf 0xa0000000233fccf0 0x2a0000000233fccf

def z960 : W := mkw 0x1fdff7ff88140000 0x11fdff7ff8814000 0xfffffffffc3fc0ff 0xffffffffffc3fc0f

def z961 : W := mkw 0x00c262df80000000 0x100c262df8000000 0x11e63e4fc000000e 0xc11e63e4fc000000

def z962 : W := mkw 0x00e22a43636a4d53 0x800e22a43636a4d5 0xb1e63e4fe3f8cffe 0xeb1e63e4fe3f8cff

def z963 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e03e4fc000000a 0x011e03e4fc000000

def z964 : W := mkw 0x802008006b7e4c53 0x0802008006b7e4c5 0xa0000000233fccf0 0x2a0000000233fccf

def z965 : W := mkw 0x6ff727673e9cea35 0x06ff727673e9cea3 0x9fe606063c18c030 0x99fe606063c18c03

def z966 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e03849c000000e 0x411e03849c000000

def z967 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x6019f9f9c3c73fcb 0x06019f9f9c3c73fc

def z968 : W := mkw 0x1fdff7ff8400a000 0x11fdff7ff8400a00 0x9ffffffffc00c00f 0xd9ffffffffc00c00

def z969 : W := mkw 0x1fdff7ff80080011 0x11fdff7ff8008001 0x1fffffffc018003f 0xd1fffffffc018003

def z970 : W := mkw 0x1fdfb77780000000 0x11fdfb7778000000 0x1ffe3ff7c000000b 0xd1ffe3ff7c000000

def z971 : W := mkw 0x1bdaf7ff80000000 0x11bdaf7ff8000000 0x11f839f1c0000002 0x011f839f1c000000

def z972 : W := mkw 0x00c262db80000000 0x000c262db8000000 0x11e63fffc000000e 0xc11e63fffc000000

def z973 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x4019f9f1c3e73f07 0x64019f9f1c3e73f0

def z974 : W := mkw 0x148ff09f80000000 0x1148ff09f8000000 0x11e7f80fc0000006 0xc11e7f80fc000000

def z975 : W := mkw 0x1fdfb76300000000 0x01fdfb7630000000 0x1fffffffc000000f 0xd1fffffffc000000

def z976 : W := mkw 0x39dab2738c15b0ac 0x139dab2738c15b0a 0xf1f83871fc3ff0f2 0x2f1f83871fc3ff0f

def z977 : W := mkw 0x1d9fb01380000000 0x11d9fb0138000000 0x1ffff801c0000007 0xd1ffff801c000000

def z978 : W := mkw 0x5fdff7ff9480a200 0x15fdff7ff9480a20 0xfffffffffcc0f30f 0xffffffffffcc0f30

def z979 : W := mkw 0x4b300d2077a8ee53 0x04b300d2077a8ee5 0xee1801b03ff8fff1 0x3ee1801b03ff8fff

def z980 : W := mkw 0x1ddfb27380000000 0x11ddfb2738000000 0x1ff9f871c0000003 0x11ff9f871c000000

def z981 : W := mkw 0x00c2224300080011 0x000c222430008001 0x11e63e4fc018003e 0xc11e63e4fc018003

def z982 : W := mkw 0x199ab01080000000 0x0199ab0108000000 0x11f83871c0000002 0x011f83871c000000

def z983 : W := mkw 0x0020080063284c53 0x00020080063284c5 0x200000000300ccf0 0x0200000000300ccf

def z984 : W := mkw 0x26250d046f3cec77 0x026250d046f3cec7 0xae0606063f38ccf0 0xbae0606063f38ccf

def z985 : W := mkw 0x1d9ff09f80000000 0x11d9ff09f8000000 0x1fe7f80fc0000004 0x91fe7f80fc000000

def z986 : W := mkw 0x00a2280363280453 0x000a228036328045 0xb1e63e0fe338c0fe 0xeb1e63e0fe338c0f

def z987 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11f9f871c0000007 0x411f9f871c000000

def z988 : W := mkw 0x9dbfb0003a9c0000 0x09dbfb0003a9c000 0xdffff8003c3f0007 0xfdffff8003c3f000

def z989 : W := mkw 0x9fdff7ff98d71188 0x99fdff7ff98d7118 0x5fffffffdcc7330f 0xd5fffffffdcc7330

def z990 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffff80e3fff00f7 0xfdffff80e3fff00f

def z991 : W := mkw 0x424047f88401fb88 0x8424047f88401fb8 0x200007f00000ff08 0x0200007f00000ff0

def z992 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xfffff9803fff300f 0xffffff9803fff300

def z993 : W := mkw 0x1f9ff5bf80000000 0x11f9ff5bf8000000 0x1ffff9bfc0000007 0xd1ffff9bfc000000

def z994 : W := mkw 0x04afb8002b7e0000 0x004afb8002b7e000 0xdffff8003fff0007 0xfdffff8003fff000

def z995 : W := mkw 0x1bdab77380000000 0x11bdab7738000000 0x1ff83e71c0000002 0x91ff83e71c000000

def z996 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xdff801f03fc03f03 0xfdff801f03fc03f0

def z997 : W := mkw 0x1fdff7cf00000000 0x01fdff7cf0000000 0x1fffffcfc000000f 0xd1fffffcfc000000

def z998 : W := mkw 0x4b7007603688ea11 0x04b7007603688ea1 0xfff807f03fd8ff3b 0xffff807f03fd8ff3

def z999 : W := mkw 0x9dbfb8037bfe0453 0x09dbfb8037bfe045 0xfffffe0fffffc0ff 0xffffffe0fffffc0f

def z1000 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x6019f9f1c3c73f0b 0x66019f9f1c3c73f0

def z1001 : W := mkw 0x1fdff7ff80011088 0x11fdff7ff8001108 0x7fffffffc3e73fcf 0xf7fffffffc3e73fc

def z1002 : W := mkw 0x19daf2fb80000000 0x119daf2fb8000000 0x11f9f9f1c0000003 0x011f9f9f1c000000

def z1003 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee1fc7be3cfff3fd 0xfee1fc7be3cfff3f

def z1004 : W := mkw 0x0d3d98003bf60000 0x00d3d98003bf6000 0xdffff8003fff0007 0xfdffff8003fff000

def z1005 : W := mkw 0x5fdff7ff90800200 0x15fdff7ff9080020 0x1fffffffc0c0030f 0xd1fffffffc0c0030

def z1006 : W := mkw 0x624047ec0401faac 0x0624047ec0401faa 0x200007f00000ff08 0x0200007f00000ff0

def z1007 : W := mkw 0x9dbfb8007bfe0442 0x09dbfb8007bfe044 0xfffff8003fff0cc7 0xffffff8003fff0cc

def z1008 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1e63e0fe038c0fc 0xeb1e63e0fe038c0f

def z1009 : W := mkw 0x1ddfb27388140000 0x11ddfb2738814000 0xdffff871fc3f0007 0xfdffff871fc3f000

def z1010 : W := mkw 0xbf1dd5bc9cd7b0ac 0x1bf1dd5bc9cd7b0a 0x4e19c1b01cc73001 0x14e19c1b01cc7300

def z1011 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee07c78e3ffffffd 0xfee07c78e3ffffff

def z1012 : W := mkw 0x3fdfb7778c14a024 0x13fdfb7778c14a02 0x9ffe3e77fc18c032 0x99ffe3e77fc18c03

def z1013 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0xbffffffffc18f0ff 0xdbffffffffc18f0f

def z1014 : W := mkw 0x66254d8c7ff7ffee 0x866254d8c7ff7ffe 0xee07c78e3ffffffd 0xfee07c78e3ffffff

def z1015 : W := mkw 0x0958d2f880000000 0x00958d2f88000000 0x11f9f9f9c000000f 0x411f9f9f9c000000

def z1016 : W := mkw 0xdfdff7ff9cd6a200 0x1dfdff7ff9cd6a20 0x5fffffffdcc7330f 0xd5fffffffdcc7330

def z1017 : W := mkw 0x3fdff7ff8c14a024 0x13fdff7ff8c14a02 0xdffffffffc3fc03f 0xfdffffffffc3fc03

def z1018 : W := mkw 0x948ff89fc97f15ca 0x9948ff89fc97f15c 0x0007f80fc03f00c4 0x00007f80fc03f00c

def z1019 : W := mkw 0x3bdaf7ff8401b0ac 0x13bdaf7ff8401b0a 0x31f83fffc000f0fa 0x031f83fffc000f0f

def z1020 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xae07c60e3c3fc0fc 0xfae07c60e3c3fc0f

def z1021 : W := mkw 0x1fdfb76700000000 0x11fdfb7670000000 0x1ffffe4fc000000f 0xd1ffffe4fc000000

def z1022 : W := mkw 0x202008006f3cec77 0x0202008006f3cec7 0xa00000003f38ccf0 0x2a00000003f38ccf

def z1023 : W := mkw 0x660545ac0c15b2ac 0x0660545ac0c15b2a 0xee07c7be3c3ff3fd 0xfee07c7be3c3ff3f

def z1024 : W := mkw 0x0b50076000000000 0x00b5007600000000 0x1ff83ff9c000000f 0xd1ff83ff9c000000

def z1025 : W := mkw 0x9dbfb8007bfe0542 0x89dbfb8007bfe054 0xdffff8003fff0f07 0xfdffff8003fff0f0

def z1026 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1fe7ff8fc000000d 0xd1fe7ff8fc000000

def z1027 : W := mkw 0x1fdff7ff88151088 0x11fdff7ff8815108 0xfffffffffc3f30cf 0xffffffffffc3f30c

def z1028 : W := mkw 0x00c2224300000000 0x000c222430000000 0x31e63e4fc000c0fe 0xc31e63e4fc000c0f

def z1029 : W := mkw 0x22c267cf0401b0ac 0x022c267cf0401b0a 0x31e63fcfc000f0fe 0xc31e63fcfc000f0f

def z1030 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1e63e4fe318ccfa 0x8b1e63e4fe318ccf

def z1031 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0xdffffffffc3f300f 0xfdffffffffc3f300

def z1032 : W := mkw 0x1fdff7ff8c14a000 0x11fdff7ff8c14a00 0xfffffffffc3ff00f 0xffffffffffc3ff00

def z1033 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1e63e4fe038ccfc 0x8b1e63e4fe038ccf

def z1034 : W := mkw 0x00200800636b5ddb 0x800200800636b5dd 0x6000000003e73fc0 0x26000000003e73fc

def z1035 : W := mkw 0xd9faba6373ea4e53 0x0d9faba6373ea4e5 0x11f83871c3c00f02 0x011f83871c3c00f0

def z1036 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1fe7fe4fc000000e 0xd1fe7fe4fc000000

def z1037 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11e03801c0000000 0x011e03801c000000

def z1038 : W := mkw 0x9d9fb80019fe0000 0x09d9fb80019fe000 0x5ffff8001cff0007 0xd5ffff8001cff000

def z1039 : W := mkw 0x0930000032800000 0x0093000003280000 0xdff9c0003fe70007 0xfdff9c0003fe7000

def z1040 : W := mkw 0x1fdff7ff80431188 0x91fdff7ff8043118 0x7fffffffc0e733cf 0xf7fffffffc0e733c

def z1041 : W := mkw 0x9d3d90003ad60000 0x09d3d90003ad6000 0xdff9c0003cc70001 0x9dff9c0003cc7000

def z1042 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfff807fe3fc0fffb 0xffff807fe3fc0fff

def z1043 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x11ffffffc000000e 0x011ffffffc000000

def z1044 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xfffff8083fff00cf 0xffffff8083fff00c

def z1045 : W := mkw 0x0020488863295cdb 0x00020488863295cd 0xe001c188233ffcfd 0x6e001c188233ffcf

def z1046 : W := mkw 0x24c762cf081510ac 0x024c762cf081510a 0x11e7fe4fc03f00fe 0xc11e7fe4fc03f00f

def z1047 : W := mkw 0x9dbfb8033bfe0000 0x09dbfb8033bfe000 0xdffff80fffff0007 0xfdffff80fffff000

def z1048 : W := mkw 0x9dbfb8003bfe4800 0x09dbfb8003bfe480 0xfffff8003fffcc07 0xffffff8003fffcc0

def z1049 : W := mkw 0x4b7007633680ea11 0x04b7007633680ea1 0xfff807f63fc0ff3b 0xffff807f63fc0ff3

def z1050 : W := mkw 0x1ddfb24308140000 0x01ddfb2430814000 0xfffffe4ffc3fc0ff 0xffffffe4ffc3fc0f

def z1051 : W := mkw 0x00c2224340004c53 0x000c2224340004c5 0xb1e63e4fe038ccfe 0xeb1e63e4fe038ccf

def z1052 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ffff9f1c0000007 0xd1ffff9f1c000000

def z1053 : W := mkw 0x1ddff2ff80000000 0x11ddff2ff8000000 0x11f9f871c0000002 0x011f9f871c000000

def z1054 : W := mkw 0x802008007bff5ddb 0x8802008007bff5dd 0xe00000003ffffff0 0x2e00000003ffffff

def z1055 : W := mkw 0x224047cc0401f8ac 0x0224047cc0401f8a 0x200007ce0000fcf8 0x0200007ce0000fcf

def z1056 : W := mkw 0xa6254d8c7ffffcff 0x0a6254d8c7ffffcf 0xee07c78e3ffffcfd 0xfee07c78e3ffffcf

def z1057 : W := mkw 0x5fdff7ff9480a200 0x15fdff7ff9480a20 0x7fffffffdfc03f0f 0xf7fffffffdfc03f0

def z1058 : W := mkw 0x3fdff7ff8c57b1ac 0x93fdff7ff8c57b1a 0x5fffffffdcc7330f 0xd5fffffffdcc7330

def z1059 : W := mkw 0x26254d8c6f3dfcff 0x026254d8c6f3dfcf 0xee01c1803f3ffcf1 0x3ee01c1803f3ffcf

def z1060 : W := mkw 0xc02008007ffeee53 0x0c02008007ffeee5 0xe00000003ffffff0 0x2e00000003ffffff

def z1061 : W := mkw 0x2605459c8c15b1ac 0x82605459c8c15b1a 0xee07c7be3c3ff3fd 0xfee07c7be3c3ff3f

def z1062 : W := mkw 0x40e22a6363284e53 0x040e22a6363284e5 0xb1e63e7fe338cffe 0xeb1e63e7fe338cff

def z1063 : W := mkw 0x0020080063295cdb 0x00020080063295cd 0xe0000000233ffcf0 0x2e0000000233ffcf

def z1064 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xfffff8403fff0c0f 0xffffff8403fff0c0

def z1065 : W := mkw 0x9fdff7ff98940000 0x19fdff7ff9894000 0x1fffffffdc00000f 0xd1fffffffdc00000

def z1066 : W := mkw 0x1fd767ef00000000 0x11fd767ef0000000 0x1fe7ffcfc000000f 0xd1fe7ffcfc000000

def z1067 : W := mkw 0x842548887bff15ca 0x8842548887bff15c 0xee07c1883fff3fcd 0xfee07c1883fff3fc

def z1068 : W := mkw 0x9dbfb8073bfe0000 0x19dbfb8073bfe000 0xdffff8063fff0007 0xfdffff8063fff000

def z1069 : W := mkw 0x240500000c15b0ac 0x0240500000c15b0a 0xee07c60e3c3ff0fd 0xfee07c60e3c3ff0f

def z1070 : W := mkw 0x4020080077a0ee42 0x04020080077a0ee4 0xe00000003fe0ffc0 0x2e00000003fe0ffc

def z1071 : W := mkw 0x19d2226300000000 0x119d222630000000 0x11e03841c0000002 0x011e03841c000000

def z1072 : W := mkw 0x6b7007643680ea24 0x06b7007643680ea2 0xfff807f63fc0ff3b 0xffff807f63fc0ff3

def z1073 : W := mkw 0x80e22a4373ea4c53 0x080e22a4373ea4c5 0xb1e63e4fe3f8ccfe 0xeb1e63e4fe3f8ccf

def z1074 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x31e63e4fc338ccfe 0x031e63e4fc338ccf

def z1075 : W := mkw 0x802008007bfe4c53 0x0802008007bfe4c5 0xc00000003fff0c00 0x2c00000003fff0c0

def z1076 : W := mkw 0x5fdff7ff8400ea00 0x15fdff7ff8400ea0 0xfffffffffc00ff0f 0xffffffffffc00ff0

def z1077 : W := mkw 0x026007402600e800 0x0026007402600e80 0xfff807f03fc0ff0b 0xffff807f03fc0ff0

def z1078 : W := mkw 0xa02008007fffb5ee 0x8a02008007fffb5e 0xe00000003ffffff0 0x2e00000003ffffff

def z1079 : W := mkw 0x9db720003a9c0000 0x09db720003a9c000 0x9fe7c0003c3f0004 0x99fe7c0003c3f000

def z1080 : W := mkw 0x1ddfb24300000000 0x01ddfb2430000000 0x1ffff841c0000007 0xd1ffff841c000000

def z1081 : W := mkw 0x00600a4363284c53 0x000600a4363284c5 0xa00006062338ccf0 0x2a00006062338ccf

def z1082 : W := mkw 0x20c222430c15b0ac 0x020c222430c15b0a 0xf1e63e4ffc3ff0fe 0xef1e63e4ffc3ff0f

def z1083 : W := mkw 0x0020080073a84c53 0x00020080073a84c5 0xe00000003ff8ccf0 0x2e00000003ff8ccf

def z1084 : W := mkw 0x1dbfb80033e20000 0x01dbfb80033e2000 0xdffff8003fe70007 0xfdffff8003fe7000

def z1085 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0x5ff807f01fc03f0b 0xd5ff807f01fc03f0

def z1086 : W := mkw 0x9d3dd898fbff15ca 0x89d3dd898fbff15c 0xee19c1b03fff3fc1 0x3ee19c1b03fff3fc

def z1087 : W := mkw 0x0020080063284c53 0x00020080063284c5 0x2000000003200cc0 0x22000000003200cc

def z1088 : W := mkw 0x9db728003bfe0000 0x09db728003bfe000 0xdfe7c0003fff0005 0xfdfe7c0003fff000

def z1089 : W := mkw 0x00c2227380000000 0x100c222738000000 0x11e03871c0000002 0x011e03871c000000

def z1090 : W := mkw 0x2008d89cc16315ee 0x82008d89cc16315e 0x6019f9ffc3e73fff 0x66019f9ffc3e73ff

def z1091 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x6019f9f1c3e73fc3 0x26019f9f1c3e73fc

def z1092 : W := mkw 0x5fdff7ff80004a00 0x15fdff7ff80004a0 0x1fffffffc0000f0f 0xd1fffffffc0000f0

def z1093 : W := mkw 0x3f1dd5bc8c57b1ac 0x93f1dd5bc8c57b1a 0x4e19c1b01cc73301 0x14e19c1b01cc7330

def z1094 : W := mkw 0x00caf2db80000000 0x000caf2db8000000 0x11e7fe4fc000000e 0xc11e7fe4fc000000

def z1095 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1fe3fffe338ccff 0xeb1fe3fffe338ccf

def z1096 : W := mkw 0x0b500f60416315ca 0x80b500f60416315c 0x7ff807f003e73fcb 0xf7ff807f003e73fc

def z1097 : W := mkw 0x624047ff8401faac 0x1624047ff8401faa 0x200007ffc000fff8 0x0200007ffc000fff

def z1098 : W := mkw 0x1fdff7ff80011088 0x11fdff7ff8001108 0x1fffffffc02700cf 0xd1fffffffc02700c

def z1099 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0x7ff807f01fc0ff0b 0x17ff807f01fc0ff0

def z1100 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ff9f9f9c000000f 0x51ff9f9f9c000000

def z1101 : W := mkw 0xbfdff7ff9cd7b0ac 0x1bfdff7ff9cd7b0a 0xfffffffffcfff0ff 0xffffffffffcfff0f

def z1102 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xf1e7fe4fe33fccff 0xef1e7fe4fe33fccf

def z1103 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee07c7fe3c3ffffd 0xfee07c7fe3c3ffff

def z1104 : W := mkw 0x00c2224300000000 0x000c222430000000 0x31e63e4fc02000ce 0xe31e63e4fc02000c

def z1105 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x71f839f1c3c03f0b 0x671f839f1c3c03f0

def z1106 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffff8003cff0005 0x9dffff8003cff000

def z1107 : W := mkw 0x9d3d98007bfe4c53 0x09d3d98007bfe4c5 0xee19c0003fffccf1 0x3ee19c0003fffccf

def z1108 : W := mkw 0x0d15000008140000 0x00d1500000814000 0xdfffc0003c3f0007 0xfdfffc0003c3f000

def z1109 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee07c7863c3ff0f1 0xbee07c7863c3ff0f

def z1110 : W := mkw 0x2605459c8c15b0ac 0x02605459c8c15b0a 0xee07c7fffc3ff0fd 0xfee07c7fffc3ff0f

def z1111 : W := mkw 0x0082200000000000 0x0008220000000000 0x11e63849c000000e 0xc11e63849c000000

def z1112 : W := mkw 0x2425488c6b3d5cff 0x02425488c6b3d5cf 0xa007c00e233fccf4 0x2a007c00e233fccf

def z1113 : W := mkw 0x9dbfb8007bfe4c53 0x09dbfb8007bfe4c5 0xfffffe0e3fffccff 0xffffffe0e3fffccf

def z1114 : W := mkw 0x4020080077a8ee53 0x04020080077a8ee5 0xe00000003fc0ff00 0x2e00000003fc0ff0

def z1115 : W := mkw 0x00e2224322004800 0x000e222432200480 0xb1e63e4fe338ccfe 0xeb1e63e4fe338ccf

def z1116 : W := mkw 0x0040024000000000 0x0004002400000000 0x11e03e49c000000e 0xc11e03e49c000000

def z1117 : W := mkw 0x9d9ff09898d71188 0x89d9ff09898d7118 0x5ffff9f9dcc7330f 0xd5ffff9f9dcc7330

def z1118 : W := mkw 0x0008980041620442 0x0000898004162044 0x6019f9f9c3e73fcf 0x66019f9f9c3e73fc

def z1119 : W := mkw 0x00c262cb00011088 0x000c262cb0001108 0x71e7ffcfc02730cf 0xe71e7ffcfc02730c

def z1120 : W := mkw 0x199af09880000000 0x0199af0988000000 0x11f9f9f9c000000f 0x411f9f9f9c000000

def z1121 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x3fffffffc02000cf 0xf3fffffffc02000c

def z1122 : W := mkw 0x4b5007601480a200 0x04b5007601480a20 0x7ff807f01fc03f0b 0xf7ff807f01fc03f0

def z1123 : W := mkw 0x9dbfb8007bfe0442 0x09dbfb8007bfe044 0xfffffe4fffffccff 0xffffffe4fffffccf

def z1124 : W := mkw 0x1bdaf7fb80000000 0x11bdaf7fb8000000 0x1ff9fff9c000000f 0xd1ff9fff9c000000

def z1125 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0x9ffffffffc3fc0ff 0xd9ffffffffc3fc0f

def z1126 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffffe063fffc037 0xfdffffe063fffc03

def z1127 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0xffe7ff8ffc3ff0fd 0xfffe7ff8ffc3ff0f

def z1128 : W := mkw 0x260505040c15b0ac 0x0260505040c15b0a 0xee07c6063c3ff0f5 0xfee07c6063c3ff0f

def z1129 : W := mkw 0x00cab25380000000 0x000cab2538000000 0x11fe3e7fc000000e 0xc11fe3e7fc000000

def z1130 : W := mkw 0x9d3d98003bfe0000 0x09d3d98003bfe000 0xdff9c0003fff0003 0xfdff9c0003fff000

def z1131 : W := mkw 0x9dbfb8037bfe4c53 0x09dbfb8037bfe4c5 0xfffff80fffffccf7 0xffffff80fffffccf

def z1132 : W := mkw 0x1d9fb00000000000 0x01d9fb0000000000 0x1ffff849c000000f 0xd1ffff849c000000

def z1133 : W := mkw 0x00200800636a4d53 0x800200800636a4d5 0x0000000003c00f00 0x00000000003c00f0

def z1134 : W := mkw 0x9db728003bbc0000 0x09db728003bbc000 0xdfe7f8003f3f0007 0xfdfe7f8003f3f000

def z1135 : W := mkw 0x9db720003a9c0000 0x09db720003a9c000 0xdfe7c0003c1f0001 0x9dfe7c0003c1f000

def z1136 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0x3fffffffc03ff0ff 0xd3fffffffc03ff0f

def z1137 : W := mkw 0x3fdff7ff8401b0ac 0x13fdff7ff8401b0a 0xbfffffffe038f0ff 0xfbfffffffe038f0f

def z1138 : W := mkw 0x7f1dd5bc9c95b2ac 0x17f1dd5bc9c95b2a 0x4e19c1b01cc73301 0x14e19c1b01cc7330

def z1139 : W := mkw 0x00a2280363284c53 0x000a2280363284c5 0xa00600062338ccf0 0x2a00600062338ccf

def z1140 : W := mkw 0x0040024000000000 0x0004002400000000 0xb1e006402000c00a 0xeb1e006402000c00

def z1141 : W := mkw 0x802008007bbc4c53 0x0802008007bbc4c5 0xa00000003f38ccf0 0x2a00000003f38ccf

def z1142 : W := mkw 0x260545bc8c15b0ac 0x1260545bc8c15b0a 0xee07c7be3c3ff0fd 0xfee07c7be3c3ff0f

def z1143 : W := mkw 0x14cff2df80000000 0x114cff2df8000000 0x11e7f84fc0000006 0x011e7f84fc000000

def z1144 : W := mkw 0x00c2224300000000 0x000c222430000000 0x31e63e4fc3000c0e 0xe31e63e4fc3000c0

def z1145 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xce07c60e3c3fc0f5 0xfce07c60e3c3fc0f

def z1146 : W := mkw 0x06254d8c63284c53 0x006254d8c63284c5 0xae07c78e2338ccfd 0xfae07c78e2338ccf

def z1147 : W := mkw 0xdff727633e9cea11 0x0dff727633e9cea1 0x9fe606063c18c030 0x99fe606063c18c03

def z1148 : W := mkw 0x00204888636b5ddb 0x800204888636b5dd 0xe007c78e23fffffd 0xee007c78e23fffff

def z1149 : W := mkw 0x5fdff7ff8400ea00 0x15fdff7ff8400ea0 0x7fffffffc3c0ff0f 0xf7fffffffc3c0ff0

def z1150 : W := mkw 0x8020080073ea4c53 0x08020080073ea4c5 0x0000000003c00c00 0x00000000003c00c0

def z1151 : W := mkw 0x602008007fbdfeff 0x0602008007fbdfef 0xe00000003ffffff0 0x2e00000003ffffff

def z1152 : W := mkw 0x3fdff7ff881510ac 0x13fdff7ff881510a 0x1fffffffc007000f 0xd1fffffffc007000

def z1153 : W := mkw 0x1dbfb0003a940000 0x01dbfb0003a94000 0xdffff8003fff0007 0xfdffff8003fff000

def z1154 : W := mkw 0x0020080063284c53 0x00020080063284c5 0x800000002318cc30 0x0800000002318cc3

def z1155 : W := mkw 0x1d9ff09f80000000 0x11d9ff09f8000000 0x11fff80fc0000006 0x011fff80fc000000

def z1156 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ffff9ffc0000007 0x11ffff9ffc000000

def z1157 : W := mkw 0x1d9ff09f80000000 0x11d9ff09f8000000 0x1ffff9ffc000000f 0xd1ffff9ffc000000

def z1158 : W := mkw 0x00e2224322084811 0x000e222432208481 0xb1e63e4fe038c0fe 0xeb1e63e4fe038c0f

def z1159 : W := mkw 0x9fdff7ff881c0000 0x19fdff7ff881c000 0x1fffffffc018000f 0xd1fffffffc018000

def z1160 : W := mkw 0x9dbfb8037bfe0453 0x09dbfb8037bfe045 0xdffff801ffff0007 0xfdffff801ffff000

def z1161 : W := mkw 0x224047ec0401b0ac 0x0224047ec0401b0a 0x200007fe0000f0f8 0x0200007fe0000f0f

def z1162 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xf1fe3e4fe3f8ccff 0xef1fe3e4fe3f8ccf

def z1163 : W := mkw 0x4020080073e35fca 0x84020080073e35fc 0x6000000003e73fc0 0x26000000003e73fc

def z1164 : W := mkw 0x4020080073e24f42 0x84020080073e24f4 0x0000000003c00f00 0x00000000003c00f0

def z1165 : W := mkw 0x4bd227631480a200 0x04bd227631480a20 0x5ffe3fffdcc0330f 0xd5ffe3fffdcc0330

def z1166 : W := mkw 0x3d9ff09f881510ac 0x13d9ff09f881510a 0xdffff80ffc3f00f7 0xfdffff80ffc3f00f

def z1167 : W := mkw 0x042500002a140000 0x0042500002a14000 0xdfe7c0003f3f0007 0xfdfe7c0003f3f000

def z1168 : W := mkw 0x5bdab7738400ea00 0x15bdab7738400ea0 0x31f83ff1c000ff0a 0x031f83ff1c000ff0

def z1169 : W := mkw 0x4020080073a84e53 0x04020080073a84e5 0xa000000023f8cff0 0x2a000000023f8cff

def z1170 : W := mkw 0x9d3d98003bfe0000 0x09d3d98003bfe000 0x4e19c0001fc70001 0x14e19c0001fc7000

def z1171 : W := mkw 0x1ddfb27380000000 0x11ddfb2738000000 0x11fff871c0000006 0x011fff871c000000

def z1172 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xf1e63fcfe338fcff 0xef1e63fcfe338fcf

def z1173 : W := mkw 0x00c2224300000000 0x000c222430000000 0x91e63e4fe018c03e 0xc91e63e4fe018c03

def z1174 : W := mkw 0x1fdff7ff80431188 0x91fdff7ff8043118 0x7fffffffc3c73f0f 0xf7fffffffc3c73f0

def z1175 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xffe63e4fff38ccff 0xfffe63e4fff38ccf

def z1176 : W := mkw 0x1f9ff5bc80000000 0x11f9ff5bc8000000 0x1ffff9f9c000000f 0xd1ffff9f9c000000

def z1177 : W := mkw 0x0bd2276300000000 0x00bd227630000000 0x1ff83ff1c000000b 0xd1ff83ff1c000000

def z1178 : W := mkw 0x0d3500003a940000 0x00d3500003a94000 0xdff9c0003fc70003 0xfdff9c0003fc7000

def z1179 : W := mkw 0x424047ffc401ffca 0x9424047ffc401ffc 0x200007ffc000ffc8 0x0200007ffc000ffc

def z1180 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x91e63e0fe338c0f6 0xe91e63e0fe338c0f

def z1181 : W := mkw 0x09d2226300000000 0x009d222630000000 0x11fe3e7fc000000e 0xc11fe3e7fc000000

def z1182 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x9ffff8003c3f0007 0xd9ffff8003c3f000

def z1183 : W := mkw 0xc02008007fffffca 0x8c02008007fffffc 0xe00000003fffffc0 0x2e00000003fffffc

def z1184 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfffe07f03ff8ff0f 0xffffe07f03ff8ff0

def z1185 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0x8e07c78e3c3fc0fd 0xd8e07c78e3c3fc0f

def z1186 : W := mkw 0x14cff2df80000000 0x114cff2df8000000 0x11e7fe0fc0000004 0x811e7fe0fc000000

def z1187 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11f839f1c000000b 0x411f839f1c000000

def z1188 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x6019ffffc3e7ffff 0x66019ffffc3e7fff

def z1189 : W := mkw 0x36cff7df8c15b0ac 0x136cff7df8c15b0a 0xffe7ffcffc3ff0ff 0xfffe7ffcffc3ff0f

def z1190 : W := mkw 0x3fdff7ff881510ac 0x13fdff7ff881510a 0xdffffffffc3f00ff 0xfdffffffffc3f00f

def z1191 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x9fffffffe018c03f 0xd9fffffffe018c03

def z1192 : W := mkw 0x0bd267ff80000000 0x10bd267ff8000000 0x1ffe3fffc000000f 0xd1ffe3fffc000000

def z1193 : W := mkw 0x99faba53f3ea4d53 0x899faba53f3ea4d5 0x11f83871c3c00f02 0x011f83871c3c00f0

def z1194 : W := mkw 0x424047e80401fa88 0x0424047e80401fa8 0x200007f80000ffc8 0x0200007f80000ffc

def z1195 : W := mkw 0x0082200300000000 0x0008220030000000 0x0006380fc03800f4 0x00006380fc03800f

def z1196 : W := mkw 0x3f9ff59f8c15b0ac 0x13f9ff59f8c15b0a 0xffffff8ffc3ff0ff 0xfffffff8ffc3ff0f

def z1197 : W := mkw 0x0b70076032800000 0x00b7007603280000 0xfff807f03fc03f0b 0xffff807f03fc03f0

def z1198 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x91e63e4fe338ccf6 0x891e63e4fe338ccf

def z1199 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1fffffbfc0000005 0x91fffffbfc000000

def z1200 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11fe3fffc000000f 0xc11fe3fffc000000

def z1201 : W := mkw 0x1fdff7ff8401b088 0x11fdff7ff8401b08 0xfffffffffc27f0cf 0xffffffffffc27f0c

def z1202 : W := mkw 0x1ddfb27780000000 0x11ddfb2778000000 0x11fe3877c0000002 0x011fe3877c000000

def z1203 : W := mkw 0x09304098f28115ca 0x809304098f28115c 0xfff801f9ffc03fcb 0xffff801f9ffc03fc

def z1204 : W := mkw 0x26254d8c6f7ffdff 0x826254d8c6f7ffdf 0xee07c78e3ffffffd 0xfee07c78e3ffffff

def z1205 : W := mkw 0x1d9ff09888151088 0x01d9ff0988815108 0xfffff9f9fc3f30cf 0xffffff9f9fc3f30c

def z1206 : W := mkw 0x84a728003bfe0000 0x084a728003bfe000 0xdfe7f8003fff0007 0xfdfe7f8003fff000

def z1207 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ffffe7fc0000006 0x91ffffe7fc000000

def z1208 : W := mkw 0x00caf2db80000000 0x000caf2db8000000 0x11f9f9f9c000000f 0x411f9f9f9c000000

def z1209 : W := mkw 0x0020080063635dca 0x80020080063635dc 0xe000000023e7ffc0 0x2e000000023e7ffc

def z1210 : W := mkw 0x00e2224362084c53 0x000e2224362084c5 0xb1e63e4fe018ccfe 0xcb1e63e4fe018ccf

def z1211 : W := mkw 0x260505040c14a024 0x0260505040c14a02 0xee07c60e3c3fc0fd 0xfee07c60e3c3fc0f

def z1212 : W := mkw 0x00c262cb00000000 0x000c262cb0000000 0x11e7ffcfc000000f 0xc11e7ffcfc000000

def z1213 : W := mkw 0x00200800636a4d53 0x800200800636a4d5 0xa000000023f8cff0 0x2a000000023f8cff

def z1214 : W := mkw 0x09d2224300000000 0x009d222430000000 0x1ffe3e4fc000000f 0xd1ffe3e4fc000000

def z1215 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa00000402338ccfa 0x6a00000402338ccf

def z1216 : W := mkw 0x0b58d7ff80000000 0x10b58d7ff8000000 0x1ff9ffffc000000f 0xd1ff9ffffc000000

def z1217 : W := mkw 0x26c767cf0c15b0ac 0x026c767cf0c15b0a 0x5fe7ffcfdc07300f 0xd5fe7ffcfdc07300

def z1218 : W := mkw 0x0020080063284c53 0x00020080063284c5 0x8000000023380c00 0x28000000023380c0

def z1219 : W := mkw 0xdff727673e9cea00 0x1dff727673e9cea0 0x9fe606063c18c000 0x99fe606063c18c00

def z1220 : W := mkw 0x19daf2fb80011088 0x119daf2fb8001108 0x71f9f9f9c02730cf 0x671f9f9f9c02730c

def z1221 : W := mkw 0x99bab80033ea0000 0x099bab80033ea000 0xdff9f8003fe70007 0xfdff9f8003fe7000

def z1222 : W := mkw 0x34cff2df881510ac 0x134cff2df881510a 0xb1e7fe4fe03fc0fe 0xeb1e7fe4fe03fc0f

def z1223 : W := mkw 0x1bdaf7ff80000000 0x11bdaf7ff8000000 0x1ff83fffc000000b 0xd1ff83fffc000000

def z1224 : W := mkw 0x9dbfb810fbfe0542 0x89dbfb810fbfe054 0xfffff9f1ffff3f0f 0xffffff9f1ffff3f0

def z1225 : W := mkw 0x1f5dd7fc80000000 0x11f5dd7fc8000000 0x1ff9fff9c000000f 0xd1ff9fff9c000000

def z1226 : W := mkw 0x1d97200008140000 0x01d9720000814000 0xdfe7c0003c3f0005 0xfdfe7c0003c3f000

def z1227 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11fe3e77c0000002 0x811fe3e77c000000

def z1228 : W := mkw 0x02c2276300000000 0x002c227630000000 0x11e63fffc000000e 0xc11e63fffc000000

def z1229 : W := mkw 0x26cff7df8c15b0ac 0x026cff7df8c15b0a 0xfffffffffc3ff0ff 0xffffffffffc3ff0f

def z1230 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xfffffe003fffc00f 0xffffffe003fffc00

def z1231 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0x7fffffffdc07f0ff 0xd7fffffffdc07f0f

def z1232 : W := mkw 0x22a26d8c2729b0ac 0x022a26d8c2729b0a 0xb1e63f8e2338f0fe 0xeb1e63f8e2338f0f

def z1233 : W := mkw 0x0b58977080000000 0x00b5897708000000 0x1ff83ff1c000000b 0xd1ff83ff1c000000

def z1234 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1fe3e7fe3f8cffe 0xeb1fe3e7fe3f8cff

def z1235 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x4019c1b003c73f01 0x04019c1b003c73f0

def z1236 : W := mkw 0x00caf2db80431188 0x800caf2db8043118 0x51ffffffc0c7330f 0xc51ffffffc0c7330

def z1237 : W := mkw 0x1ddff2ff80000000 0x11ddff2ff8000000 0x11e7f80fc0000004 0x011e7f80fc000000

def z1238 : W := mkw 0x9dbfb810fbfe0542 0x89dbfb810fbfe054 0xdffff801ffff0007 0xfdffff801ffff000

def z1239 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x601ff9ffc3ff3fff 0x6601ff9ffc3ff3ff

def z1240 : W := mkw 0x00cafadbc16315ca 0x800cafadbc16315c 0xf1ffffffe3ffffff 0xef1ffffffe3fffff

def z1241 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee07c60e3c3ff0f4 0xbee07c60e3c3ff0f

def z1242 : W := mkw 0x4b7007673680ea00 0x14b7007673680ea0 0xfff807f63fc0ff0b 0xffff807f63fc0ff0

def z1243 : W := mkw 0x02c267ff80000000 0x102c267ff8000000 0x11e03fffc000000a 0x011e03fffc000000

def z1244 : W := mkw 0x42489f600562ea00 0x042489f600562ea0 0x6019fff003e7ff0f 0x66019fff003e7ff0

def z1245 : W := mkw 0x0bd227630400a000 0x00bd227630400a00 0xfffe3ffffc38f0ff 0xffffe3ffffc38f0f

def z1246 : W := mkw 0x5fdff7ff94c3b388 0x95fdff7ff94c3b38 0x5fffffffdcc7330f 0xd5fffffffdcc7330

def z1247 : W := mkw 0x1fd7276700000000 0x11fd727670000000 0x1fe63e0fc0000004 0x91fe63e0fc000000

def z1248 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11f83e71c000000a 0xc11f83e71c000000

def z1249 : W := mkw 0x9dbfb8007bfe0442 0x09dbfb8007bfe044 0xfffff9f9ffff3fcf 0xffffff9f9ffff3fc

def z1250 : W := mkw 0x00c2224300000000 0x000c222430000000 0x91e63e4fe038000e 0xe91e63e4fe038000

def z1251 : W := mkw 0x06cff7df80000000 0x006cff7df8000000 0x1fffffffc000000f 0xd1fffffffc000000

def z1252 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffff9b03fff3307 0xfdffff9b03fff330

def z1253 : W := mkw 0x0020080063204c42 0x00020080063204c4 0xa00000002320ccc0 0x2a00000002320ccc

def z1254 : W := mkw 0x7fdff7ff9c95b2ac 0x17fdff7ff9c95b2a 0x5fffffffdcc7330f 0xd5fffffffdcc7330

def z1255 : W := mkw 0x00200800636b5ddb 0x800200800636b5dd 0xa0000000233fccf0 0x2a0000000233fccf

def z1256 : W := mkw 0x1fdff7ff80431188 0x91fdff7ff8043118 0x1fffffffc007000f 0xd1fffffffc007000

def z1257 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdfe7f8003c3f0005 0xfdfe7f8003c3f000

def z1258 : W := mkw 0x9dbfb810fbfe0542 0x89dbfb810fbfe054 0xfffff879ffff0fcf 0xffffff879ffff0fc

def z1259 : W := mkw 0x9dbfb810bbfe0100 0x89dbfb810bbfe010 0xdffff8303fff0307 0xfdffff8303fff030

def z1260 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa00606062338ccf0 0xaa00606062338ccf

def z1261 : W := mkw 0x624047ec0401faac 0x0624047ec0401faa 0x2000078e0000f0f8 0x02000078e0000f0f

def z1262 : W := mkw 0x00200800636b15ca 0x800200800636b15c 0xe000000023ff3fc0 0x2e000000023ff3fc

def z1263 : W := mkw 0x9dbfb8007bfe0442 0x09dbfb8007bfe044 0xdffff809ffff00c7 0xfdffff809ffff00c

def z1264 : W := mkw 0x99dab27390c20000 0x199dab27390c2000 0x11f83871c0c00002 0x011f83871c0c0000

def z1265 : W := mkw 0x402008006728ee53 0x0402008006728ee5 0xa00000002338fff0 0x2a00000002338fff

def z1266 : W := mkw 0x00004888412114ca 0x000004888412114c 0x6019f9f9c3e73fcf 0x66019f9f9c3e73fc

def z1267 : W := mkw 0xddbfb8203bfe0200 0x0ddbfb8203bfe020 0xdffff8303fff0307 0xfdffff8303fff030

def z1268 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa00600002338ccf4 0xea00600002338ccf

def z1269 : W := mkw 0x14cff2df80000000 0x114cff2df8000000 0x11ffffffc000000f 0xc11ffffffc000000

def z1270 : W := mkw 0x8020080073ea0542 0x88020080073ea054 0x0000000003c00f00 0x00000000003c00f0

def z1271 : W := mkw 0x02c2274300000000 0x002c227430000000 0x1fe63fcfc000000f 0xd1fe63fcfc000000

def z1272 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee1fc78e3ffff0ff 0xfee1fc78e3ffff0f

def z1273 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ffffe0fc0000007 0xd1ffffe0fc000000

def z1274 : W := mkw 0x10cab25380000000 0x110cab2538000000 0x11e63e4fc000000e 0xc11e63e4fc000000

def z1275 : W := mkw 0x3fdff7ff8c14a024 0x13fdff7ff8c14a02 0xbffffffffc38c0ff 0xfbffffffffc38c0f

def z1276 : W := mkw 0xbfdff7ff9cd7b0ac 0x1bfdff7ff9cd7b0a 0x5fffffffdcc7300f 0xd5fffffffdcc7300

def z1277 : W := mkw 0x9dbfb8007bfe0442 0x09dbfb8007bfe044 0xdffff841ffff0c07 0xfdffff841ffff0c0

def z1278 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa006000e2338ccf4 0x2a006000e2338ccf

def z1279 : W := mkw 0x493000003680ea00 0x0493000003680ea0 0xfff801f03fc0ff0b 0xffff801f03fc0ff0

def z1280 : W := mkw 0x26c767ff8c15b0ac 0x126c767ff8c15b0a 0xffe7fffffc3ff0ff 0xfffe7fffffc3ff0f

def z1281 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xdff807f03fc0ff03 0x9dff807f03fc0ff0

def z1282 : W := mkw 0x1d9fb80009760000 0x01d9fb8000976000 0xdffff8003fff0007 0xfdffff8003fff000

def z1283 : W := mkw 0x9dbfb0003ade0000 0x09dbfb0003ade000 0xdfffc0003fdf0003 0xfdfffc0003fdf000

def z1284 : W := mkw 0x1bdab77380000000 0x11bdab7738000000 0x1ffe3fffc000000f 0xd1ffe3fffc000000

def z1285 : W := mkw 0x9fdff7ff88560000 0x19fdff7ff8856000 0x1fffffffc007000f 0xd1fffffffc007000

def z1286 : W := mkw 0x02caf7ff80000000 0x102caf7ff8000000 0x11ffffffc000000f 0xc11ffffffc000000

def z1287 : W := mkw 0x42600f606728ee53 0x042600f606728ee5 0xa00007f02338fff8 0x2a00007f02338fff

def z1288 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x1ff83871c0000003 0xd1ff83871c000000

def z1289 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee07c7ce3f3ffcff 0xfee07c7ce3f3ffcf

def z1290 : W := mkw 0x9fdff7ff98d60000 0x19fdff7ff98d6000 0xdffffffffcff000f 0xfdffffffffcff000

def z1291 : W := mkw 0x09bab80033ea0000 0x009bab80033ea000 0xdffff8003fff0007 0xfdffff8003fff000

def z1292 : W := mkw 0x00e22a43636a4c53 0x000e22a43636a4c5 0xf1e63e4fe3ffccfe 0xef1e63e4fe3ffccf

def z1293 : W := mkw 0x0020080063295ddb 0x80020080063295dd 0xa00000002338fff0 0x2a00000002338fff

def z1294 : W := mkw 0x00cab25380000000 0x000cab2538000000 0x11f83871c0000002 0x011f83871c000000

def z1295 : W := mkw 0x9d9fb00018d60000 0x09d9fb00018d6000 0x5fffc0001cc70001 0x95fffc0001cc7000

def z1296 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xae07c78e3c3ff0fc 0x9ae07c78e3c3ff0f

def z1297 : W := mkw 0x1fdff7ff80004800 0x11fdff7ff8000480 0x3fffffffc000cc0f 0xd3fffffffc000cc0

def z1298 : W := mkw 0x224047cf0401f8bd 0x0224047cf0401f8b 0x2000078e0000f0f8 0x02000078e0000f0f

def z1299 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e63e47c0000002 0x811e63e47c000000

def z1300 : W := mkw 0x06c767ff80000000 0x106c767ff8000000 0x1fe7ffffc000000f 0xd1fe7ffffc000000

def z1301 : W := mkw 0x42c227630400ea00 0x042c227630400ea0 0x31e63fffc000ff0e 0xc31e63fffc000ff0

def z1302 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0xdffff8703fff0f07 0xfdffff8703fff0f0

def z1303 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e63841c0000006 0xc11e63841c000000

def z1304 : W := mkw 0x9fdff7ff90c20000 0x19fdff7ff90c2000 0x1fffffffc0c0000f 0xd1fffffffc0c0000

def z1305 : W := mkw 0x00caf2db80011088 0x000caf2db8001108 0xf1ffffffe03ff0ff 0xef1ffffffe03ff0f

def z1306 : W := mkw 0x06c7274700000000 0x006c727470000000 0x1fe63e4fc000000e 0xd1fe63e4fc000000

def z1307 : W := mkw 0x00c2224300000000 0x000c222430000000 0x71fe3fffc3c03f0f 0xe71fe3fffc3c03f0

def z1308 : W := mkw 0xa02008007ffffcff 0x0a02008007ffffcf 0xe00000003ffffcf0 0x2e00000003ffffcf

def z1309 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0x2019f9f9c3e73fce 0x02019f9f9c3e73fc

def z1310 : W := mkw 0x9dbfb8003bfe0000 0x09dbfb8003bfe000 0x9ffff8003fff0006 0x99ffff8003fff000

def z1311 : W := mkw 0x3fdff7ff8c14a024 0x13fdff7ff8c14a02 0xfffffffffc18f03f 0xffffffffffc18f03

def z1312 : W := mkw 0x0020080063280442 0x0002008006328044 0xa000000023380cc0 0x2a000000023380cc

def z1313 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0xe019fff9e3e7ffcf 0xee019fff9e3e7ffc

def z1314 : W := mkw 0x3fdff7ff8401b0ac 0x13fdff7ff8401b0a 0xfffffffffc00f0ff 0xffffffffffc00f0f

def z1315 : W := mkw 0x02c227430400a000 0x002c227430400a00 0xffe63fcffc00f00f 0xfffe63fcffc00f00

def z1316 : W := mkw 0x49faba73f3ea4f53 0x849faba73f3ea4f5 0x11f83871c3c00f02 0x011f83871c3c00f0

def z1317 : W := mkw 0x00c2224300000000 0x000c222430000000 0x11e6384fc0000006 0x011e6384fc000000

def z1318 : W := mkw 0x00600a4063204c42 0x000600a4063204c4 0xb1e63e4fe338ccfe 0xeb1e63e4fe338ccf

def z1319 : W := mkw 0x4bf227633680ea00 0x04bf227633680ea0 0xfffe3ffffff8ffff 0xffffe3ffffff8fff

def z1320 : W := mkw 0x3fdff7ff8c15b0ac 0x13fdff7ff8c15b0a 0x9fe7fe0ffc3fc0f4 0x99fe7fe0ffc3fc0f

def z1321 : W := mkw 0x00e22a4373a84c53 0x000e22a4373a84c5 0xf1e63e4ffff8ccfe 0xef1e63e4ffff8ccf

def z1322 : W := mkw 0x1fdfb77780000000 0x11fdfb7778000000 0x1ffe3e7fc000000e 0xd1ffe3e7fc000000

def z1323 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xe01801f023f8fffb 0x6e01801f023f8fff

def z1324 : W := mkw 0x02c267cf00000000 0x002c267cf0000000 0x11e63fcfc000000e 0xc11e63fcfc000000

def z1325 : W := mkw 0x1ddff2db80000000 0x01ddff2db8000000 0x1fffffffc000000f 0xd1fffffffc000000

def z1326 : W := mkw 0x26c727470c14a024 0x026c727470c14a02 0x9fe63e4ffc18c03e 0xd9fe63e4ffc18c03

def z1327 : W := mkw 0x14c7224700000000 0x114c722470000000 0x11e63e4fc000000e 0xc11e63e4fc000000

def z1328 : W := mkw 0x66254d8c7fbdfeff 0x066254d8c7fbdfef 0xee07c78e3ffffffd 0xfee07c78e3ffffff

def z1329 : W := mkw 0x04c7224308140000 0x004c722430814000 0xdfe7fe4ffc3f000f 0xfdfe7fe4ffc3f000

def z1330 : W := mkw 0x1ddff2ff80000000 0x11ddff2ff8000000 0x11fff9ffc000000f 0x411fff9ffc000000

def z1331 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xb1e63fffe338fffe 0xeb1e63fffe338fff

def z1332 : W := mkw 0x4b38ddb8f7e3ffca 0x84b38ddb8f7e3ffc 0xee19c1b03fe7ffc1 0x3ee19c1b03fe7ffc

def z1333 : W := mkw 0x802008007bfe0442 0x0802008007bfe044 0xe00000003fff0cc0 0x2e00000003fff0cc

def z1334 : W := mkw 0x0020080063280453 0x0002008006328045 0x80000000233800f0 0x280000000233800f

def z1335 : W := mkw 0x94afb8002b7e0000 0x094afb8002b7e000 0xdfe7f8003f3f0007 0xfdfe7f8003f3f000

def z1336 : W := mkw 0x04c7224300000000 0x004c722430000000 0x1fe7fe4fc000000f 0xd1fe7fe4fc000000

def z1337 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1ffe3fffc000000a 0x91ffe3fffc000000

def z1338 : W := mkw 0x0020080063284c53 0x00020080063284c5 0xa00000002300cc00 0x2a00000002300cc0

def z1339 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0xf1e63e4fe3f8fffe 0xef1e63e4fe3f8fff

def z1340 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x5fffffffc3c0000f 0xf5fffffffc3c0000

def z1341 : W := mkw 0x0918d09880000000 0x00918d0988000000 0x1ff9f9f9c000000f 0xd1ff9f9f9c000000

def z1342 : W := mkw 0x1fd7276700000000 0x11fd727670000000 0x1ffe3fffc000000f 0xd1ffe3fffc000000

def z1343 : W := mkw 0x1bdaf7ff80000000 0x11bdaf7ff8000000 0x11fe3fffc000000e 0xc11fe3fffc000000

def z1344 : W := mkw 0x9ddfb27398d60000 0x19ddfb27398d6000 0x5ff9f871dcc70003 0x15ff9f871dcc7000

def z1345 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x3fffffffc3000c0f 0xf3fffffffc3000c0

def z1346 : W := mkw 0xb48ff89cc97f15ee 0x8b48ff89cc97f15e 0x0007f80fc03f00f4 0x00007f80fc03f00f

def z1347 : W := mkw 0x8020080073ea4c53 0x08020080073ea4c5 0xa000000023f8ccf0 0x2a000000023f8ccf

def z1348 : W := mkw 0x008af09880000000 0x0008af0988000000 0x11fff9f9c000000f 0xc11fff9f9c000000

def z1349 : W := mkw 0x0bdaf7fb80000000 0x00bdaf7fb8000000 0x1fffffffc000000f 0xd1fffffffc000000

def z1350 : W := mkw 0x4020080077a8ee53 0x04020080077a8ee5 0xa00000003f38ccf0 0x2a00000003f38ccf

def z1351 : W := mkw 0x02c2276700000000 0x102c227670000000 0x11e63e4fc000000e 0xc11e63e4fc000000

def z1352 : W := mkw 0x042508006b3c4c53 0x0042508006b3c4c5 0xee07c0003f3fccf5 0xfee07c0003f3fccf

def z1353 : W := mkw 0x1ddfb27380000000 0x11ddfb2738000000 0x1ffffe7fc000000f 0xd1ffffe7fc000000

def z1354 : W := mkw 0x19daf2fb80000000 0x119daf2fb8000000 0x11f9f879c0000006 0x011f9f879c000000

def z1355 : W := mkw 0x1fdff7ff80011088 0x11fdff7ff8001108 0x5fffffffc007300f 0xd5fffffffc007300

def z1356 : W := mkw 0x1fdff7ff80011188 0x91fdff7ff8001118 0x1fffffffc000330f 0xd1fffffffc000330

def z1357 : W := mkw 0x0b3005003680a000 0x00b3005003680a00 0xfff807f03fc0ff0b 0xffff807f03fc0ff0

def z1358 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfff807f83fe0ffcf 0xffff807f83fe0ffc

def z1359 : W := mkw 0x1bdab7738400a000 0x11bdab7738400a00 0xfff83ff1fc00f00b 0xffff83ff1fc00f00

def z1360 : W := mkw 0x1fd767ff80000000 0x11fd767ff8000000 0x1fe63fffc000000e 0xd1fe63fffc000000

def z1361 : W := mkw 0x0048d2d880000000 0x00048d2d88000000 0x11f9fff9c000000f 0xc11f9fff9c000000

def z1362 : W := mkw 0x1fdff7f880000000 0x01fdff7f88000000 0x1ffffff9c000000f 0xd1ffffff9c000000

def z1363 : W := mkw 0x3f9ff59c8c15b0ac 0x03f9ff59c8c15b0a 0xfffffffffc3ff0ff 0xffffffffffc3ff0f

def z1364 : W := mkw 0x0970024032804800 0x0097002403280480 0xfff807f03fc0ff0b 0xffff807f03fc0ff0

def z1365 : W := mkw 0x1fdff7ff80000000 0x11fdff7ff8000000 0x1fffffffc3c00f0f 0xd1fffffffc3c00f0

def z1366 : W := mkw 0x3fdff7ff8401b0ac 0x13fdff7ff8401b0a 0x7fffffffc027f0ff 0xf7fffffffc027f0f

def z1367 : W := mkw 0x002008006b3c4c53 0x0002008006b3c4c5 0xe00000003f3fccf0 0x2e00000003f3fccf

def z1368 : W := mkw 0x3fdff7cf0c15b0ac 0x03fdff7cf0c15b0a 0xffffffcffc3ff0ff 0xfffffffcffc3ff0f

def z1369 : W := mkw 0x19daf2fb80000000 0x119daf2fb8000000 0x11ffffffc000000f 0xc11ffffffc000000

def z1370 : W := mkw 0x00cab24300000000 0x000cab2430000000 0x11fffe4fc000000f 0xc11fffe4fc000000

def z1371 : W := mkw 0x3fd727670c14a024 0x13fd727670c14a02 0xbfe63e4ffc38c0fe 0xfbfe63e4ffc38c0f

def z1372 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xbff807f03fc0ff0a 0x9bff807f03fc0ff0

def z1373 : W := mkw 0x0000000000000000 0x0000000000000000 0x20003849c02000ce 0x620003849c02000c

def z1374 : W := mkw 0x4b7007603680ea00 0x04b7007603680ea0 0xfff9c7f03fe7ff0f 0xffff9c7f03fe7ff0

def z1375 : W := mkw 0x22204d8c6729fcff 0x022204d8c6729fcf 0xa000078e2338fcf8 0x2a000078e2338fcf

def z1376 : W := mkw 0x00c2224300000000 0x000c222430000000 0xb1e63e4fe000c00e 0xeb1e63e4fe000c00

def z1377 : W := mkw 0x2405408c081510ac 0x02405408c081510a 0xee07c60e3c3fc0fd 0xfee07c60e3c3fc0f

def z1378 : W := mkw 0x19dab27380000000 0x119dab2738000000 0x11f83e7fc000000a 0x011f83e7fc000000

def z1379 : W := mkw 0x19dab24300000000 0x019dab2430000000 0x11fe3e4fc000000e 0xc11fe3e4fc000000

def z1380 : W := mkw 0x00e22a4363284c53 0x000e22a4363284c5 0x91e63e4fe038c0fe 0xc91e63e4fe038c0f

def z1381 : W := mkw 0x5fdff7ff8400a200 0x15fdff7ff8400a20 0x1fffffffc000330f 0xd1fffffffc000330

def z1382 : W := mkw 0x2605458c0c15b0ac 0x02605458c0c15b0a 0xee1fc7fe3c3ff0ff 0xfee1fc7fe3c3ff0f

def z1383 : W := mkw 0x0008d898c16315ca 0x80008d898c16315c 0xe01ff9f9e3ff3fcf 0xee01ff9f9e3ff3fc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z8,z9,z3,z5,z6]),(0,[z1,z2,z10,z8,z3,z5,z11]),(0,[z1,z2,z8,z12,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z13,z6]),(0,[z1,z2,z14,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z15,z6]),(1,[z1,z16,z17,z3,z5,z6]),(0,[z1,z2,z18,z8,z3,z5,z6])],[(0,[z1,z19,z2,z8,z3,z5,z6]),(0,[z20,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z21,z5,z6])],[(0,[z22,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z23,z6])],[(1,[z1,z2,z24,z3,z5,z6]),(0,[z1,z2,z8,z3,z25,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z26]),(0,[z1,z2,z8,z3,z5,z27,z6]),(0,[z1,z2,z8,z3,z5,z28,z6]),(0,[z1,z2,z3,z4,z29,z5,z6]),(1,[z1,z2,z8,z3,z5,z30])],[(0,[z31,z1,z2,z3,z5,z32,z6]),(0,[z33,z1,z34,z8,z3,z5,z6]),(1,[z1,z17,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z35,z36,z6]),(0,[z1,z2,z8,z3,z5,z6,z37]),(0,[z1,z2,z38,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z39,z5,z6]),(0,[z1,z2,z40,z41,z3,z5,z6])],[(0,[z1,z2,z42,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z43]),(0,[z1,z44,z2,z8,z3,z5,z6]),(0,[z45,z2,z8,z3,z46,z5,z6]),(0,[z0,z1,z2,z8,z3,z5,z47]),(0,[z1,z2,z48,z8,z49,z5,z6]),(0,[z1,z2,z8,z3,z5,z50,z6])],[(0,[z33,z1,z44,z8,z3,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z51,z5,z6]),(0,[z1,z2,z10,z3,z4,z5,z6]),(0,[z1,z2,z52,z8,z3,z5,z6])]],
   [[(0,[z53,z1,z2,z8,z54,z5,z6]),(0,[z1,z55,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z56,z6]),(0,[z1,z2,z57,z8,z3,z5,z6]),(0,[z1,z2,z58,z8,z3,z5,z32]),(0,[z1,z2,z8,z3,z5,z6,z59]),(0,[z1,z2,z60,z3,z51,z5,z6])],[(0,[z1,z2,z38,z61,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z62,z6]),(0,[z45,z1,z2,z8,z3,z46,z6]),(0,[z1,z2,z3,z4,z63,z5,z6]),(0,[z1,z2,z64,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z65]),(0,[z1,z2,z66,z8,z3,z5,z6])],[(0,[z1,z2,z8,z8,z3,z5,z6]),(0,[z1,z67,z2,z8,z3,z5,z6]),(0,[z1,z16,z2,z3,z68,z5,z6]),(1,[z1,z2,z8,z3,z69,z6]),(1,[z1,z2,z8,z49,z5,z70])],[(0,[z1,z17,z2,z3,z5,z71,z6]),(0,[z1,z2,z8,z72,z3,z5,z6])],[(0,[z1,z16,z2,z58,z3,z5,z6]),(0,[z73,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z74,z6]),(1,[z1,z2,z48,z8,z5,z75])],[(0,[z76,z1,z2,z8,z3,z5,z6]),(1,[z1,z2,z8,z3,z5,z77]),(0,[z1,z2,z8,z3,z5,z78,z6]),(0,[z79,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z80]),(0,[z81,z1,z2,z8,z3,z5,z6])],[(0,[z82,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z83,z54,z3,z5,z6]),(0,[z1,z2,z7,z3,z4,z5,z6])],[(0,[z31,z1,z2,z84,z3,z5,z6]),(0,[z85,z1,z2,z86,z3,z5,z6]),(0,[z53,z1,z2,z8,z87,z5,z6]),(0,[z73,z1,z88,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z89,z5,z6]),(0,[z1,z90,z2,z8,z3,z5,z6])]],
   [[(0,[z91,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z92,z93,z3,z5,z6]),(0,[z1,z2,z48,z8,z3,z5,z94]),(0,[z95,z1,z2,z8,z3,z5,z6]),(1,[z1,z88,z8,z96,z5,z6])],[(0,[z1,z2,z8,z97,z3,z5,z6]),(0,[z31,z1,z16,z2,z3,z5,z6]),(0,[z98,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z99,z6])],[(0,[z1,z2,z8,z100,z3,z5,z6]),(0,[z1,z2,z101,z8,z3,z5,z6]),(1,[z1,z2,z102,z3,z5,z6]),(0,[z1,z2,z8,z103,z3,z5,z6])],[(0,[z1,z2,z8,z3,z104,z5,z6]),(0,[z1,z2,z8,z3,z5,z105,z6]),(0,[z1,z88,z2,z8,z106,z5,z6]),(0,[z1,z2,z3,z106,z4,z5,z6]),(0,[z1,z2,z107,z8,z3,z5,z6]),(1,[z1,z2,z108,z3,z5,z6])],[(1,[z1,z109,z2,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z32,z6]),(0,[z73,z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z110,z8,z3,z5,z6]),(0,[z1,z8,z3,z5,z11,z6,z37]),(1,[z1,z111,z8,z3,z5,z11]),(0,[z1,z2,z8,z3,z5,z6,z112])],[(0,[z1,z2,z93,z3,z5,z113,z6]),(0,[z1,z2,z8,z3,z5,z114,z6]),(1,[z1,z2,z115,z8,z3,z5]),(0,[z1,z111,z2,z48,z8,z3,z5]),(0,[z1,z116,z2,z8,z3,z5,z6])],[(0,[z1,z2,z117,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z118,z6])],[(0,[z33,z1,z2,z8,z119,z5,z6]),(0,[z1,z2,z120,z8,z3,z5,z6]),(0,[z1,z2,z121,z8,z3,z5,z6])]],
   [[(0,[z1,z2,z8,z119,z3,z5,z6]),(0,[z1,z2,z8,z3,z122,z5,z6]),(0,[z1,z2,z123,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z124,z6])],[(0,[z125,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z126,z5,z6]),(0,[z1,z2,z58,z8,z3,z5,z127]),(0,[z1,z128,z2,z8,z3,z5,z6])],[(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z1,z129,z2,z3,z4,z5,z6])],[(0,[z1,z2,z8,z130,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z47,z6]),(0,[z1,z17,z2,z3,z5,z6,z127])],[(0,[z1,z17,z2,z131,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z32,z6]),(0,[z1,z2,z48,z132,z3,z5,z6])],[(1,[z1,z2,z8,z3,z5,z133]),(0,[z1,z2,z83,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z134,z5,z6]),(0,[z1,z2,z135,z8,z3,z5,z6]),(0,[z1,z136,z2,z8,z3,z137,z6]),(0,[z1,z2,z138,z8,z3,z5,z6])],[(0,[z33,z1,z2,z139,z3,z5,z6]),(0,[z1,z2,z8,z140,z3,z5,z6]),(0,[z1,z16,z2,z84,z3,z5,z6]),(0,[z1,z2,z131,z8,z3,z5,z11]),(0,[z1,z2,z141,z8,z3,z5,z6])],[(0,[z2,z8,z54,z3,z87,z5,z6]),(0,[z1,z17,z2,z3,z5,z142,z6]),(0,[z73,z1,z8,z3,z106,z5,z6]),(0,[z1,z2,z8,z3,z5,z143,z6]),(0,[z1,z2,z58,z8,z49,z3,z5])]],
   [[(0,[z1,z17,z2,z93,z3,z5,z6]),(0,[z1,z2,z8,z144,z3,z5,z6]),(0,[z33,z1,z2,z145,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z146,z6]),(0,[z1,z16,z16,z2,z3,z5,z6]),(0,[z73,z1,z7,z8,z3,z5,z6]),(0,[z1,z2,z38,z49,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z147,z6]),(0,[z1,z2,z10,z8,z3,z5,z32])],[(1,[z1,z2,z8,z3,z5,z148]),(0,[z1,z2,z149,z38,z3,z5,z6]),(0,[z1,z150,z2,z8,z3,z5,z6]),(0,[z1,z2,z151,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z152,z5,z6]),(1,[z1,z2,z153,z8,z5,z6]),(0,[z1,z2,z8,z3,z51,z5,z37]),(0,[z1,z2,z38,z3,z5,z50,z6]),(0,[z1,z2,z154,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z155])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z38,z3,z5,z113,z6]),(0,[z1,z2,z8,z3,z156,z5,z6])],[(0,[z1,z16,z2,z3,z46,z5,z6])],[(0,[z157,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z47,z158]),(0,[z73,z1,z2,z48,z8,z5,z6]),(0,[z1,z2,z8,z3,z5,z159,z6]),(0,[z1,z2,z92,z8,z3,z5,z6]),(1,[z1,z2,z8,z160,z35,z6]),(0,[z1,z2,z49,z3,z161,z5,z6])],[(0,[z1,z17,z2,z54,z3,z5,z6]),(1,[z1,z2,z3,z68,z5,z6]),(1,[z162,z2,z8,z3,z5,z6]),(0,[z1,z163,z88,z2,z3,z5,z6]),(0,[z164,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z165,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z166,z6]),(0,[z1,z17,z2,z10,z3,z5,z6]),(0,[z167,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z168,z3,z5,z6]),(0,[z1,z2,z10,z48,z8,z3,z5]),(1,[z1,z2,z41,z3,z5,z6]),(0,[z169,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z170,z6])]],
   [[(0,[z125,z1,z2,z171,z3,z5,z6]),(0,[z1,z172,z2,z8,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z173,z6]),(0,[z1,z2,z48,z38,z3,z5,z6]),(0,[z1,z174,z2,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z6,z133]),(0,[z53,z1,z2,z8,z3,z5,z6]),(0,[z175,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z176,z6]),(0,[z1,z2,z8,z3,z5,z177,z6]),(0,[z178,z1,z2,z8,z3,z5,z6]),(0,[z1,z179,z2,z38,z3,z5,z6]),(0,[z1,z150,z2,z38,z3,z5,z6]),(0,[z1,z2,z8,z3,z180,z5,z6])],[(0,[z1,z2,z8,z3,z5,z6,z6]),(0,[z181,z1,z2,z8,z3,z5,z6]),(0,[z1,z136,z182,z8,z3,z5,z6])],[(0,[z1,z2,z183,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z184,z6]),(0,[z1,z2,z8,z3,z185,z5,z6]),(0,[z1,z16,z2,z48,z3,z5,z6]),(0,[z1,z186,z2,z8,z3,z5,z6]),(0,[z1,z2,z38,z187,z3,z5,z6]),(0,[z1,z2,z188,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z189,z5,z6])],[(0,[z1,z2,z8,z3,z46,z5,z6]),(0,[z1,z16,z2,z131,z3,z5,z6]),(0,[z1,z88,z2,z3,z4,z5,z6])],[(0,[z1,z17,z2,z42,z3,z5,z6]),(0,[z1,z2,z190,z8,z3,z5,z6]),(0,[z1,z191,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z192])],[(0,[z1,z2,z193,z8,z3,z5,z6]),(0,[z1,z2,z8,z194,z3,z5,z6]),(0,[z1,z7,z8,z96,z3,z5,z6]),(0,[z195,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z58,z8,z3,z5,z37]),(0,[z196,z1,z2,z8,z3,z5,z6])],[(0,[z197,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z102,z3,z106,z5,z6]),(0,[z1,z2,z108,z8,z3,z5,z6]),(0,[z1,z2,z92,z58,z3,z5,z6]),(0,[z1,z198,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z51,z5,z50])]],
   [[(0,[z1,z199,z2,z8,z3,z5,z6]),(0,[z200,z1,z2,z8,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z6,z37]),(0,[z1,z2,z8,z3,z5,z173,z6]),(0,[z1,z2,z201,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z35,z137,z6]),(0,[z1,z179,z2,z8,z3,z5,z11]),(1,[z1,z2,z202,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z203,z6]),(0,[z1,z2,z8,z204,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z50,z6]),(0,[z1,z16,z2,z205,z3,z5,z6]),(0,[z1,z2,z10,z8,z3,z5,z127]),(0,[z1,z2,z48,z8,z5,z6,z75])],[(0,[z125,z1,z19,z8,z3,z5,z6]),(0,[z31,z1,z2,z3,z63,z5,z6]),(0,[z1,z2,z8,z3,z5,z206,z6]),(0,[z207,z1,z2,z8,z3,z5,z6])],[(0,[z1,z208,z2,z8,z3,z5,z6]),(0,[z1,z2,z38,z3,z87,z5,z6]),(0,[z1,z2,z145,z8,z3,z5,z6]),(0,[z209,z1,z2,z8,z3,z5,z94]),(0,[z1,z16,z17,z8,z3,z5,z6]),(1,[z73,z1,z8,z106,z5,z6]),(0,[z1,z2,z205,z3,z4,z5,z6]),(0,[z1,z2,z8,z210,z3,z5,z6]),(0,[z211,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z212,z8,z3,z5,z6])],[(0,[z1,z213,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z214,z5,z6]),(0,[z1,z2,z8,z160,z87,z5,z6]),(0,[z1,z111,z2,z8,z3,z5,z37]),(0,[z1,z2,z215,z3,z4,z5,z6]),(0,[z216,z1,z2,z8,z3,z5,z6])],[(0,[z1,z17,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z217,z3,z5,z6]),(0,[z1,z136,z2,z8,z3,z36,z6]),(0,[z1,z2,z84,z3,z4,z5,z6]),(0,[z1,z2,z8,z5,z70,z6,z75]),(0,[z1,z2,z131,z8,z3,z5,z158])],[(0,[z1,z2,z218,z8,z3,z5,z6]),(0,[z219,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z220,z6]),(0,[z1,z2,z8,z35,z5,z142,z6])],[(0,[z1,z2,z8,z3,z221,z5,z6]),(0,[z1,z2,z54,z3,z4,z5,z6]),(0,[z1,z222,z2,z8,z3,z5,z6]),(0,[z1,z223,z2,z8,z3,z5,z6]),(0,[z1,z2,z92,z3,z5,z32,z6]),(0,[z1,z2,z48,z58,z8,z3,z5]),(0,[z1,z2,z10,z8,z49,z3,z5]),(0,[z1,z2,z8,z3,z5,z224,z6])]],
   [[(0,[z225,z1,z2,z8,z3,z5,z6]),(0,[z33,z1,z2,z8,z3,z46,z6]),(0,[z1,z226,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z227,z6]),(0,[z1,z2,z38,z3,z5,z32,z6])],[(0,[z1,z2,z3,z4,z5,z47,z6]),(0,[z1,z2,z8,z205,z3,z5,z6]),(0,[z1,z8,z3,z228,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z229,z6]),(0,[z1,z2,z230,z8,z3,z5,z6]),(0,[z1,z2,z58,z3,z5,z6,z127])],[(0,[z1,z2,z171,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z231,z5,z6]),(0,[z1,z16,z2,z3,z5,z6,z75]),(0,[z1,z2,z110,z96,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z232,z6])],[(0,[z1,z2,z8,z233,z3,z5,z6]),(0,[z234,z1,z17,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z235,z5,z6]),(0,[z1,z2,z236,z8,z3,z5,z6])],[(0,[z1,z2,z54,z3,z237,z5,z6]),(0,[z45,z1,z2,z8,z3,z5,z6]),(1,[z1,z16,z2,z3,z5,z6]),(0,[z1,z88,z2,z8,z96,z5,z6]),(0,[z1,z2,z238,z8,z3,z4,z5])],[(0,[z1,z239,z2,z8,z3,z5,z6]),(1,[z1,z2,z240,z8,z3,z6]),(0,[z73,z1,z17,z8,z3,z5,z6]),(1,[z1,z129,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z241])],[(0,[z31,z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z242]),(0,[z1,z2,z8,z3,z5,z6,z243]),(0,[z1,z2,z8,z3,z244,z5,z6])],[(0,[z1,z2,z38,z3,z5,z71,z6]),(0,[z1,z2,z245,z8,z3,z5,z6]),(0,[z1,z136,z17,z2,z3,z5,z6]),(0,[z1,z17,z2,z58,z3,z5,z6]),(0,[z1,z2,z40,z8,z3,z5,z6])]],
   [[(0,[z1,z2,z8,z3,z5,z11,z47]),(0,[z1,z111,z17,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z246,z6]),(0,[z247,z1,z2,z8,z3,z5,z6]),(0,[z225,z1,z2,z38,z3,z5,z6])],[(0,[z73,z1,z2,z8,z3,z248,z6]),(0,[z1,z2,z8,z3,z5,z249,z6]),(0,[z1,z2,z8,z49,z3,z5,z70]),(0,[z1,z2,z8,z3,z5,z6,z250])],[(0,[z19,z2,z42,z8,z3,z5,z6]),(1,[z1,z2,z8,z3,z5,z251]),(0,[z1,z2,z8,z252,z3,z5,z6]),(0,[z1,z2,z115,z8,z3,z106,z5]),(0,[z1,z2,z8,z3,z5,z6,z75])],[(0,[z1,z253,z2,z8,z3,z5,z6]),(0,[z209,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z254,z8,z3,z5,z6]),(0,[z1,z2,z8,z255,z3,z106,z5]),(0,[z1,z2,z256,z8,z3,z5,z6])],[(0,[z45,z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z257,z8,z3,z5,z6])],[(0,[z258,z1,z2,z8,z3,z5,z6]),(0,[z85,z1,z2,z259,z3,z5,z6]),(1,[z1,z2,z8,z3,z5,z62]),(0,[z1,z16,z2,z8,z3,z5,z6]),(0,[z1,z2,z40,z8,z5,z142,z6])],[(0,[z125,z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z260,z8,z3,z5,z6]),(0,[z209,z0,z2,z8,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z36,z6]),(0,[z1,z2,z10,z8,z3,z5,z37]),(0,[z1,z2,z8,z261,z3,z5,z6]),(0,[z1,z2,z8,z3,z262,z5,z6]),(0,[z1,z2,z8,z3,z5,z263,z6])],[(0,[z53,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z24,z3,z5,z71,z6]),(0,[z1,z264,z2,z8,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z32,z6]),(0,[z1,z16,z182,z2,z3,z5,z6]),(0,[z1,z2,z3,z126,z4,z5,z6]),(0,[z265,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z41,z8,z3,z5,z6])]],
   [[(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z267,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z268,z5,z6]),(0,[z1,z2,z8,z3,z269,z5,z6]),(0,[z0,z1,z2,z8,z3,z51,z5]),(0,[z1,z136,z8,z3,z5,z36,z6]),(0,[z1,z270,z2,z8,z3,z5,z6])],[(0,[z271,z1,z2,z8,z3,z5,z6]),(0,[z272,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z273,z3,z5,z6]),(0,[z1,z2,z8,z274,z3,z5,z6]),(0,[z1,z275,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z276,z5,z6]),(0,[z1,z2,z8,z3,z63,z5,z6]),(0,[z1,z2,z8,z132,z3,z5,z6])],[(0,[z1,z17,z8,z96,z3,z5,z6]),(1,[z1,z16,z7,z3,z5,z6]),(0,[z1,z2,z8,z3,z248,z5,z6]),(1,[z1,z2,z84,z3,z113,z6])],[(1,[z1,z2,z171,z3,z5,z6]),(0,[z1,z2,z8,z277,z3,z5,z6]),(0,[z0,z1,z17,z2,z3,z5,z6]),(0,[z73,z1,z2,z273,z3,z5,z6]),(0,[z1,z2,z84,z8,z3,z63,z6])],[(0,[z1,z278,z17,z2,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z70,z6])],[(0,[z1,z19,z2,z38,z3,z5,z6]),(0,[z53,z1,z2,z8,z3,z5,z251]),(1,[z1,z2,z14,z8,z3,z5]),(0,[z1,z279,z17,z2,z3,z5,z6]),(0,[z1,z16,z2,z38,z3,z5,z6]),(0,[z258,z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z38,z3,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z280,z6]),(0,[z1,z2,z8,z3,z5,z36,z6]),(0,[z1,z2,z281,z8,z3,z5,z6]),(0,[z1,z2,z282,z8,z3,z5,z6]),(0,[z1,z2,z283,z8,z3,z5,z6]),(0,[z1,z284,z2,z8,z3,z5,z6])],[(1,[z1,z2,z8,z3,z285,z6]),(0,[z1,z8,z3,z137,z5,z36,z6]),(0,[z1,z2,z38,z3,z5,z6,z127]),(0,[z1,z286,z2,z8,z3,z5,z6])]],
   [[(0,[z266,z125,z2,z8,z3,z5,z6]),(0,[z266,z2,z42,z8,z3,z5,z6]),(0,[z266,z1,z17,z2,z3,z5,z6]),(0,[z287,z1,z2,z3,z4,z5,z6]),(0,[z1,z182,z2,z8,z3,z5,z288]),(0,[z1,z2,z215,z8,z4,z5,z6]),(0,[z1,z2,z8,z210,z3,z4,z5]),(0,[z1,z2,z58,z3,z5,z113,z6])],[(0,[z1,z2,z42,z38,z3,z5,z6]),(0,[z1,z2,z289,z8,z3,z5,z6]),(0,[z1,z2,z240,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z290]),(0,[z1,z17,z2,z84,z3,z5,z6]),(0,[z1,z291,z2,z8,z3,z5,z6]),(0,[z1,z292,z2,z8,z3,z5,z6]),(0,[z293,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z50,z6,z158])],[(0,[z1,z2,z294,z8,z3,z5,z6]),(1,[z1,z2,z8,z152,z5,z6]),(0,[z33,z1,z17,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z295,z5,z6]),(0,[z1,z296,z17,z2,z3,z5,z6]),(0,[z1,z2,z297,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z298,z6]),(0,[z1,z2,z8,z3,z5,z299,z6]),(0,[z1,z2,z8,z3,z5,z300,z6])],[(0,[z1,z2,z8,z3,z301,z5,z6]),(0,[z1,z2,z3,z87,z4,z5,z6]),(0,[z1,z2,z302,z8,z3,z5,z6]),(0,[z1,z2,z303,z8,z3,z5,z6]),(1,[z1,z2,z8,z3,z248,z6]),(0,[z1,z2,z8,z3,z5,z304,z6]),(0,[z1,z2,z3,z4,z5,z6,z158]),(0,[z1,z2,z38,z3,z5,z142,z6])],[(0,[z266,z1,z42,z8,z3,z5,z6]),(0,[z287,z1,z2,z61,z3,z5,z6]),(0,[z1,z2,z38,z93,z3,z5,z6]),(1,[z0,z2,z8,z3,z5,z94]),(0,[z1,z163,z17,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z70,z6])],[(1,[z53,z2,z8,z54,z5,z6]),(0,[z1,z2,z305,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z306,z6]),(1,[z1,z2,z8,z3,z5,z307]),(0,[z1,z16,z2,z3,z5,z6,z94]),(0,[z1,z308,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z309,z6]),(0,[z1,z2,z310,z8,z3,z5,z142]),(0,[z1,z2,z131,z8,z49,z3,z5])],[(0,[z1,z2,z86,z8,z3,z5,z6]),(0,[z1,z2,z311,z8,z3,z5,z6]),(0,[z312,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z313,z5,z6]),(0,[z1,z2,z160,z3,z314,z5,z6])],[(0,[z1,z2,z8,z3,z5,z315,z6]),(0,[z1,z2,z8,z316,z3,z5,z6]),(0,[z1,z17,z2,z3,z46,z5,z6]),(0,[z1,z179,z2,z48,z8,z3,z5]),(1,[z1,z129,z2,z3,z5,z6]),(0,[z1,z2,z48,z131,z8,z3,z5])]],
   [[(0,[z287,z1,z17,z2,z3,z5,z6])],[(0,[z1,z16,z7,z8,z3,z5,z6]),(0,[z1,z111,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z317])],[(0,[z318,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z38,z54,z3,z5,z6]),(0,[z1,z319,z2,z8,z3,z5,z6]),(0,[z45,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z320,z6]),(1,[z1,z163,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z321]),(0,[z1,z2,z322,z8,z3,z5,z6]),(0,[z323,z1,z2,z8,z3,z5,z6])],[(0,[z1,z2,z93,z8,z3,z5,z6]),(0,[z1,z16,z2,z40,z3,z5,z6]),(1,[z1,z2,z3,z5,z27,z6])],[(0,[z1,z16,z111,z2,z3,z5,z6])],[(0,[z1,z2,z8,z324,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z71,z6]),(0,[z1,z2,z8,z3,z325,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z94]),(0,[z1,z2,z326,z8,z3,z5,z6]),(1,[z1,z2,z273,z3,z5,z6]),(0,[z1,z2,z327,z8,z3,z5,z6]),(1,[z1,z2,z132,z3,z5,z6])],[(0,[z1,z2,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z328]),(0,[z1,z17,z2,z48,z3,z5,z6]),(0,[z247,z1,z16,z2,z3,z5,z6]),(0,[z329,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z330,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z11,z6]),(0,[z1,z2,z38,z3,z5,z6,z75])],[(0,[z0,z2,z8,z3,z5,z6,z94]),(0,[z1,z17,z8,z9,z3,z5,z6])]],
   [[(0,[z331,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z332,z5,z6])],[(1,[z1,z2,z8,z3,z5,z6]),(1,[z1,z2,z8,z3,z5,z333]),(0,[z1,z2,z8,z3,z5,z6,z307]),(0,[z209,z1,z16,z2,z3,z5,z6]),(0,[z1,z334,z2,z8,z3,z5,z6]),(0,[z1,z2,z210,z3,z4,z5,z6])],[(0,[z335,z1,z2,z8,z3,z5,z6]),(0,[z2,z8,z3,z5,z47,z6,z94]),(0,[z1,z2,z8,z3,z5,z336,z6]),(0,[z1,z2,z8,z49,z3,z51,z5])],[(0,[z1,z2,z8,z3,z337,z5,z6]),(0,[z1,z2,z338,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z339,z6]),(0,[z1,z2,z8,z49,z3,z5,z47]),(0,[z258,z1,z16,z2,z3,z5,z6]),(0,[z1,z16,z2,z3,z137,z5,z6]),(0,[z1,z16,z2,z3,z35,z5,z6]),(0,[z1,z2,z8,z3,z5,z340,z6]),(0,[z1,z2,z8,z3,z5,z6,z341]),(0,[z1,z2,z8,z3,z342,z5,z6]),(0,[z1,z2,z343,z8,z3,z5,z6])],[(0,[z85,z1,z2,z8,z87,z5,z6]),(0,[z0,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z344]),(0,[z1,z2,z8,z345,z3,z5,z6]),(0,[z1,z17,z2,z205,z3,z5,z6]),(0,[z1,z346,z2,z8,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z6,z37]),(0,[z1,z2,z131,z8,z3,z5,z37]),(1,[z1,z2,z210,z3,z4,z5])],[(0,[z85,z1,z17,z2,z3,z5,z6]),(0,[z1,z2,z3,z228,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z347,z6]),(0,[z1,z2,z131,z8,z3,z51,z6])],[(0,[z1,z348,z2,z8,z3,z5,z6]),(1,[z85,z2,z8,z87,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z349]),(0,[z1,z350,z2,z8,z3,z5,z6])],[(0,[z1,z2,z8,z351,z3,z5,z6]),(0,[z1,z179,z2,z8,z49,z3,z5]),(1,[z1,z2,z8,z210,z3,z5]),(0,[z1,z352,z2,z8,z3,z5,z6])]],
   [[(0,[z1,z2,z8,z3,z353,z5,z6]),(0,[z45,z1,z2,z8,z3,z71,z6]),(0,[z1,z2,z8,z3,z354,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z355]),(0,[z1,z2,z8,z3,z5,z356,z6]),(1,[z1,z3,z228,z4,z5,z6]),(0,[z1,z2,z131,z3,z4,z5,z6]),(0,[z1,z2,z357,z8,z3,z5,z6])],[(0,[z1,z2,z358,z8,z3,z5,z6]),(0,[z2,z8,z3,z46,z5,z71,z6]),(0,[z1,z2,z8,z3,z5,z6,z359]),(0,[z1,z16,z2,z3,z106,z5,z6]),(1,[z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z38,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z360])],[(0,[z1,z2,z8,z361,z3,z5,z6]),(0,[z1,z2,z362,z8,z3,z5,z6]),(0,[z363,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z364]),(0,[z1,z2,z8,z365,z3,z5,z6]),(0,[z1,z2,z202,z8,z3,z5,z6])],[(0,[z366,z1,z17,z2,z3,z5,z6]),(0,[z367,z1,z16,z2,z3,z5,z6]),(0,[z1,z16,z2,z96,z3,z5,z6]),(0,[z1,z2,z8,z3,z137,z5,z6]),(0,[z1,z2,z8,z3,z5,z368,z6]),(0,[z1,z2,z3,z5,z113,z32,z6]),(0,[z1,z2,z8,z3,z35,z5,z6])],[(0,[z1,z2,z8,z3,z5,z6,z369]),(0,[z1,z2,z8,z3,z5,z370,z6]),(0,[z1,z16,z2,z8,z3,z5,z371]),(0,[z1,z2,z8,z3,z5,z6,z372])],[(0,[z125,z2,z8,z3,z87,z5,z6]),(0,[z1,z17,z2,z3,z5,z6,z75]),(0,[z1,z2,z3,z4,z5,z6,z127]),(1,[z1,z2,z92,z3,z63,z6])],[(0,[z1,z2,z373,z8,z3,z5,z6]),(1,[z1,z2,z3,z5,z6,z321])],[(0,[z1,z374,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z375]),(0,[z1,z2,z8,z3,z5,z376,z6]),(0,[z1,z2,z8,z377,z3,z5,z6]),(0,[z1,z2,z378,z8,z3,z5,z6])]],
   [[(0,[z1,z379,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z160,z54,z5,z6]),(0,[z1,z2,z8,z3,z380,z5,z6]),(1,[z1,z8,z3,z228,z5,z6]),(0,[z1,z2,z92,z38,z3,z5,z6]),(0,[z1,z2,z8,z381,z3,z5,z6]),(0,[z1,z2,z8,z3,z314,z5,z6])],[(0,[z1,z2,z24,z8,z3,z5,z6]),(1,[z1,z2,z3,z325,z5,z6]),(0,[z1,z2,z8,z3,z106,z5,z6]),(0,[z1,z2,z3,z4,z5,z142,z6]),(0,[z79,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z38,z38,z3,z5,z6]),(0,[z1,z2,z8,z3,z382,z5,z6]),(0,[z1,z2,z131,z8,z3,z5,z50])],[(1,[z287,z2,z61,z3,z5,z6]),(0,[z1,z2,z8,z383,z3,z5,z6]),(0,[z1,z2,z7,z8,z3,z5,z6]),(0,[z73,z1,z2,z8,z5,z70,z6]),(0,[z1,z308,z88,z2,z3,z5,z6]),(0,[z1,z2,z8,z384,z3,z5,z6]),(0,[z1,z2,z385,z8,z3,z5,z6]),(0,[z386,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z30,z6]),(0,[z1,z2,z3,z51,z5,z387,z6])],[(0,[z388,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z96,z3,z5,z6]),(0,[z1,z2,z38,z58,z3,z5,z6]),(0,[z1,z2,z8,z389,z3,z5,z6])],[(0,[z53,z1,z2,z38,z3,z5,z6]),(0,[z1,z17,z2,z3,z63,z5,z6]),(0,[z1,z2,z3,z137,z5,z27,z6]),(0,[z1,z390,z2,z8,z3,z5,z6])],[(0,[z1,z2,z391,z8,z3,z5,z6]),(0,[z1,z2,z9,z3,z4,z5,z6]),(0,[z1,z2,z8,z392,z3,z5,z6]),(0,[z1,z2,z10,z58,z3,z5,z6])],[(0,[z1,z2,z8,z3,z393,z5,z6]),(0,[z1,z8,z96,z3,z106,z5,z6]),(0,[z1,z2,z8,z3,z5,z148,z6]),(0,[z394,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z395,z8,z3,z5,z6])],[(1,[z209,z2,z8,z3,z5,z47]),(0,[z396,z1,z2,z8,z3,z5,z6]),(1,[z1,z2,z38,z205,z5,z6]),(0,[z1,z2,z38,z8,z205,z5,z6]),(0,[z1,z2,z8,z3,z397,z5,z6]),(0,[z1,z2,z398,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z399])]],
   [[(0,[z400,z1,z2,z8,z3,z5,z6]),(0,[z318,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z401,z5,z6]),(0,[z1,z2,z238,z3,z4,z5,z6]),(0,[z1,z2,z92,z8,z3,z113,z6])],[(0,[z1,z17,z2,z3,z5,z280,z6]),(0,[z1,z17,z2,z3,z5,z36,z6]),(0,[z1,z182,z2,z8,z3,z36,z6]),(1,[z1,z2,z402,z3,z5,z6]),(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z1,z2,z84,z92,z3,z5,z6]),(0,[z1,z2,z403,z8,z3,z5,z6])],[(0,[z1,z2,z3,z325,z5,z71,z6]),(0,[z1,z179,z2,z3,z4,z5,z6])],[(0,[z1,z42,z8,z3,z5,z36,z6]),(0,[z1,z2,z217,z3,z106,z5,z6]),(0,[z1,z182,z2,z3,z4,z5,z6]),(1,[z1,z2,z310,z8,z3,z5])],[(0,[z1,z404,z2,z8,z3,z5,z6]),(0,[z1,z2,z405,z8,z3,z5,z6]),(0,[z1,z2,z406,z8,z3,z5,z6])],[(0,[z1,z2,z10,z3,z5,z32,z6]),(0,[z1,z2,z407,z8,z3,z5,z6]),(0,[z1,z2,z66,z49,z3,z5,z6])],[(0,[z408,z1,z2,z8,z3,z5,z6]),(0,[z85,z1,z2,z8,z3,z5,z6]),(0,[z33,z45,z2,z8,z3,z5,z6]),(0,[z73,z1,z2,z8,z3,z5,z409]),(0,[z1,z2,z410,z3,z5,z11,z6]),(0,[z1,z129,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z30,z142])],[(0,[z1,z2,z8,z411,z3,z5,z6]),(0,[z53,z2,z8,z54,z3,z5,z6]),(0,[z1,z2,z48,z8,z3,z5,z47]),(0,[z1,z17,z2,z3,z5,z70,z6]),(0,[z1,z16,z136,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z412,z5,z6]),(0,[z1,z2,z40,z8,z3,z142,z6]),(0,[z1,z2,z8,z3,z5,z6,z413])]],
   [[(0,[z414,z1,z2,z8,z3,z5,z6]),(0,[z1,z17,z2,z38,z3,z5,z6]),(0,[z1,z16,z2,z9,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z415,z6]),(0,[z1,z2,z38,z154,z3,z5,z6])],[(0,[z1,z2,z416,z8,z3,z5,z6]),(0,[z1,z2,z115,z8,z3,z5,z6]),(1,[z1,z2,z410,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z417])],[(0,[z1,z2,z8,z3,z418,z5,z6]),(0,[z0,z1,z16,z2,z3,z5,z6]),(0,[z1,z179,z17,z2,z3,z5,z6]),(0,[z1,z16,z2,z3,z51,z5,z6]),(0,[z1,z2,z8,z255,z3,z5,z6]),(0,[z1,z2,z8,z3,z36,z142,z6]),(0,[z1,z2,z3,z4,z5,z6,z37]),(1,[z1,z2,z10,z3,z5,z32]),(1,[z1,z2,z60,z3,z5,z6])],[(0,[z1,z182,z17,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z50,z6]),(0,[z1,z2,z8,z3,z419,z5,z6])],[(0,[z1,z2,z8,z3,z5,z94,z158]),(0,[z1,z16,z2,z3,z63,z5,z6]),(0,[z1,z2,z8,z3,z5,z420,z6]),(1,[z1,z2,z238,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z1,z2,z405,z38,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z159,z6]),(1,[z1,z2,z381,z3,z5,z6]),(0,[z1,z2,z8,z3,z421,z5,z6])],[(0,[z422,z1,z2,z8,z3,z5,z6]),(0,[z1,z179,z8,z3,z5,z6,z37])],[(0,[z1,z2,z8,z3,z5,z6,z423])],[(0,[z1,z182,z42,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z424]),(0,[z1,z2,z8,z3,z29,z5,z6]),(0,[z1,z2,z425,z8,z3,z5,z6]),(1,[z1,z2,z215,z4,z5,z6])]],
   [[(0,[z1,z17,z2,z3,z5,z6,z94]),(0,[z1,z2,z8,z9,z3,z5,z6]),(1,[z1,z2,z8,z3,z5,z371]),(0,[z426,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z60,z8,z3,z5,z6])],[(0,[z33,z1,z16,z2,z3,z5,z6]),(0,[z1,z16,z2,z160,z3,z5,z6])],[(0,[z1,z2,z14,z8,z3,z5,z71]),(0,[z427,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z40,z38,z3,z5,z6]),(0,[z1,z2,z428,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z51,z5,z6])],[(0,[z1,z2,z38,z3,z46,z5,z6]),(0,[z1,z2,z8,z3,z5,z37,z75]),(0,[z1,z2,z8,z3,z5,z429,z6])],[(1,[z1,z2,z217,z3,z5,z6]),(0,[z1,z2,z8,z430,z3,z5,z6]),(0,[z1,z2,z8,z3,z431,z5,z6]),(0,[z1,z2,z160,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z432,z6]),(0,[z1,z2,z310,z8,z3,z5,z6]),(0,[z1,z2,z433,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z434,z5,z6]),(0,[z1,z2,z435,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z436]),(0,[z1,z2,z8,z3,z5,z6,z437])],[(0,[z45,z1,z2,z8,z3,z50,z6]),(0,[z209,z1,z2,z38,z3,z5,z6]),(0,[z1,z17,z2,z40,z3,z5,z6]),(0,[z1,z379,z16,z2,z3,z5,z6]),(0,[z1,z2,z8,z160,z3,z142,z6])],[(0,[z31,z1,z2,z3,z4,z5,z6]),(0,[z1,z438,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z439,z5,z6]),(0,[z73,z1,z2,z8,z106,z5,z6]),(0,[z1,z2,z8,z3,z440,z5,z6]),(1,[z1,z2,z8,z3,z5,z288]),(0,[z1,z2,z40,z8,z3,z35,z6])]],
   [[(0,[z1,z2,z441,z8,z3,z5,z6]),(0,[z442,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z443,z5,z6]),(0,[z367,z1,z2,z8,z3,z5,z6]),(0,[z1,z88,z2,z8,z3,z5,z6]),(0,[z1,z2,z108,z3,z137,z5,z6]),(2,[z1,z129,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z387,z6])],[(0,[z1,z111,z179,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z444,z5,z6]),(0,[z1,z2,z8,z160,z3,z5,z6])],[(0,[z33,z1,z2,z8,z3,z5,z62]),(0,[z1,z2,z8,z445,z3,z5,z6]),(0,[z1,z2,z8,z3,z446,z5,z6]),(0,[z1,z2,z428,z38,z3,z5,z6])],[(0,[z1,z2,z8,z447,z3,z5,z6]),(0,[z31,z1,z2,z61,z3,z5,z6]),(0,[z1,z2,z448,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z449,z6]),(0,[z1,z17,z2,z3,z354,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z450]),(1,[z1,z2,z3,z412,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z158])],[(0,[z1,z2,z8,z3,z5,z6,z451]),(0,[z1,z2,z8,z452,z3,z5,z6])],[(0,[z1,z2,z8,z453,z3,z5,z6]),(0,[z1,z2,z3,z5,z11,z6,z321])],[(0,[z1,z2,z8,z3,z454,z5,z6]),(0,[z1,z2,z8,z455,z3,z5,z6]),(0,[z1,z17,z2,z3,z137,z5,z6]),(0,[z1,z17,z2,z3,z35,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z456]),(0,[z1,z2,z84,z3,z5,z113,z6]),(0,[z1,z2,z58,z8,z3,z5,z6]),(0,[z1,z457,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z49,z3,z5,z75])],[(0,[z234,z1,z2,z8,z3,z5,z6]),(0,[z125,z1,z2,z3,z4,z5,z6]),(0,[z31,z1,z17,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z458]),(0,[z33,z1,z2,z8,z3,z71,z6]),(0,[z0,z1,z2,z8,z3,z5,z94]),(0,[z1,z2,z8,z3,z5,z47,z37]),(0,[z1,z2,z459,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z460,z5,z6]),(0,[z461,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z462,z8,z3,z5,z6]),(0,[z1,z2,z463,z8,z3,z5,z6]),(0,[z1,z2,z464,z8,z3,z5,z6])]],
   [[(0,[z1,z16,z2,z8,z3,z5,z465]),(0,[z1,z88,z2,z38,z3,z5,z6]),(0,[z1,z2,z466,z8,z3,z5,z6]),(0,[z1,z2,z215,z8,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z229,z6]),(0,[z1,z2,z38,z205,z3,z5,z6])],[(0,[z467,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z32,z6]),(0,[z1,z2,z8,z3,z51,z50,z6])],[(0,[z1,z2,z468,z8,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z6,z375]),(0,[z1,z2,z469,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z470,z6]),(1,[z1,z2,z66,z3,z5,z6])],[(0,[z125,z19,z2,z8,z3,z5,z6]),(0,[z1,z136,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z288]),(0,[z1,z2,z8,z3,z471,z5,z6])],[(0,[z85,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z472,z6]),(0,[z1,z17,z2,z3,z106,z5,z6])],[(0,[z1,z2,z8,z3,z473,z5,z6]),(0,[z1,z2,z474,z8,z3,z5,z6]),(0,[z209,z2,z8,z3,z5,z47,z6]),(0,[z1,z2,z3,z4,z475,z5,z6]),(0,[z1,z2,z3,z39,z4,z5,z6])],[(0,[z1,z19,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z476,z3,z5,z6]),(0,[z1,z17,z2,z96,z3,z5,z6]),(0,[z1,z16,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z11,z6]),(0,[z1,z2,z8,z160,z3,z35,z6])],[(0,[z125,z1,z17,z2,z3,z5,z6]),(0,[z287,z1,z2,z93,z3,z5,z6]),(0,[z33,z1,z2,z8,z152,z5,z6]),(0,[z1,z477,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z478]),(0,[z73,z226,z2,z8,z3,z5,z6]),(0,[z1,z182,z2,z8,z3,z5,z148]),(0,[z1,z2,z8,z3,z479,z5,z6]),(0,[z1,z2,z8,z3,z480,z5,z6]),(0,[z1,z2,z3,z5,z32,z6,z127]),(1,[z1,z2,z8,z3,z51,z50])]],
   [[(0,[z85,z1,z2,z8,z54,z5,z6]),(0,[z1,z2,z8,z3,z5,z69,z6]),(0,[z1,z2,z48,z8,z3,z5,z70])],[(0,[z1,z481,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z482,z5,z6]),(0,[z1,z2,z8,z3,z483,z5,z6]),(0,[z484,z1,z2,z8,z3,z5,z6])],[(0,[z1,z2,z485,z8,z3,z5,z6]),(0,[z1,z2,z42,z3,z4,z5,z6]),(0,[z1,z16,z2,z61,z3,z5,z6]),(0,[z33,z1,z2,z8,z3,z5,z307]),(0,[z1,z2,z486,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z487,z6]),(0,[z1,z2,z8,z3,z5,z488,z6])],[(0,[z1,z2,z8,z3,z5,z489,z6]),(0,[z1,z136,z2,z38,z3,z5,z6]),(0,[z1,z2,z490,z8,z3,z5,z6]),(1,[z1,z2,z378,z3,z5,z6])],[(0,[z2,z42,z8,z3,z87,z5,z6]),(1,[z1,z2,z3,z443,z5,z6]),(0,[z1,z2,z38,z9,z3,z5,z6]),(1,[z1,z2,z362,z3,z5,z6]),(0,[z1,z182,z2,z8,z3,z137,z6]),(0,[z1,z111,z2,z38,z3,z5,z6]),(0,[z1,z2,z8,z491,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z492])],[(0,[z1,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z493,z6]),(0,[z1,z88,z8,z96,z3,z5,z6]),(1,[z1,z2,z110,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z494,z6]),(0,[z1,z2,z40,z381,z3,z5,z6])],[(0,[z1,z2,z495,z8,z3,z5,z6]),(1,[z1,z16,z2,z3,z5,z371]),(0,[z1,z2,z8,z3,z5,z496,z6]),(0,[z1,z2,z8,z3,z5,z70,z11]),(0,[z1,z2,z215,z8,z205,z5,z6]),(0,[z1,z2,z8,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z497,z6]),(0,[z1,z498,z2,z8,z3,z5,z6])],[(0,[z31,z287,z2,z8,z3,z5,z6]),(0,[z1,z16,z499,z2,z3,z5,z6]),(0,[z1,z2,z92,z3,z63,z5,z6]),(0,[z500,z1,z2,z8,z3,z5,z6]),(1,[z1,z2,z40,z8,z142,z6])]],
   [[(0,[z1,z2,z8,z501,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z50,z47]),(0,[z1,z278,z2,z8,z3,z5,z6]),(0,[z427,z1,z16,z2,z3,z5,z6]),(0,[z73,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z502]),(0,[z1,z2,z8,z3,z5,z503,z6]),(0,[z1,z2,z8,z504,z3,z5,z6]),(0,[z1,z2,z38,z3,z63,z5,z6]),(0,[z1,z2,z8,z3,z5,z505,z6])],[(0,[z1,z2,z3,z4,z46,z5,z6]),(0,[z1,z2,z8,z3,z5,z506,z6]),(0,[z1,z279,z2,z8,z3,z5,z6]),(0,[z1,z88,z2,z48,z8,z5,z6]),(0,[z1,z2,z8,z3,z5,z507,z6])],[(0,[z1,z2,z8,z61,z3,z5,z6]),(0,[z1,z2,z402,z3,z5,z6,z37])],[(0,[z266,z1,z2,z8,z3,z5,z133]),(0,[z1,z2,z61,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z508,z6]),(0,[z1,z2,z8,z3,z237,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z509]),(1,[z1,z2,z3,z460,z5,z6]),(0,[z1,z2,z8,z3,z137,z142,z6]),(0,[z1,z2,z49,z3,z4,z5,z6]),(0,[z1,z2,z510,z8,z3,z5,z6]),(0,[z1,z2,z131,z8,z3,z6,z158]),(0,[z1,z511,z2,z8,z3,z5,z6])],[(0,[z266,z1,z2,z8,z3,z5,z6]),(0,[z1,z16,z19,z2,z3,z5,z6]),(1,[z1,z2,z8,z255,z3,z5]),(0,[z1,z2,z8,z3,z512,z5,z6])],[(0,[z125,z1,z2,z513,z3,z5,z6]),(0,[z1,z2,z514,z8,z3,z5,z6]),(0,[z1,z16,z179,z2,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z36,z6]),(0,[z1,z2,z38,z160,z3,z5,z6])],[(0,[z1,z296,z2,z8,z3,z5,z6]),(0,[z33,z1,z2,z8,z3,z5,z6]),(0,[z45,z1,z2,z131,z8,z3,z6]),(0,[z1,z17,z223,z2,z3,z5,z6]),(0,[z1,z2,z362,z3,z5,z36,z6]),(0,[z1,z2,z515,z8,z3,z5,z6]),(0,[z1,z516,z2,z8,z3,z5,z6]),(0,[z1,z2,z10,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z517,z5,z6]),(0,[z1,z2,z8,z518,z3,z5,z6])],[(0,[z1,z2,z8,z3,z519,z5,z6]),(1,[z1,z2,z86,z3,z5,z6]),(0,[z1,z2,z520,z8,z3,z5,z6]),(0,[z0,z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z8,z3,z521,z5,z6]),(0,[z1,z2,z402,z8,z3,z5,z6]),(0,[z522,z1,z2,z8,z3,z5,z6])]],
   [[(0,[z1,z2,z8,z3,z523,z5,z6]),(1,[z1,z2,z3,z5,z472,z6]),(0,[z73,z1,z17,z2,z3,z5,z6]),(0,[z1,z163,z2,z8,z3,z5,z6]),(0,[z524,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z96,z3,z412,z5,z6]),(1,[z1,z2,z8,z5,z415,z6]),(0,[z1,z2,z8,z3,z525,z5,z6]),(0,[z1,z2,z8,z3,z228,z5,z6])],[(0,[z1,z2,z8,z49,z3,z5,z94]),(0,[z1,z2,z8,z3,z5,z6,z526])],[(0,[z1,z2,z8,z3,z5,z527,z6]),(0,[z1,z2,z8,z528,z3,z5,z6]),(0,[z529,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z48,z8,z3,z5,z75]),(0,[z1,z530,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z531,z5,z6])],[(0,[z1,z2,z8,z3,z532,z5,z6]),(0,[z1,z533,z2,z8,z3,z5,z6]),(0,[z1,z17,z2,z9,z3,z5,z6]),(0,[z1,z16,z2,z215,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z70,z6]),(0,[z1,z2,z378,z160,z3,z5,z6])],[(0,[z1,z109,z2,z42,z3,z5,z6]),(0,[z287,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z5,z6]),(1,[z1,z2,z8,z3,z5,z465]),(0,[z1,z2,z3,z5,z503,z6,z37]),(0,[z1,z2,z8,z534,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z535,z6]),(0,[z1,z2,z8,z536,z3,z5,z6]),(0,[z1,z2,z3,z63,z5,z113,z6]),(0,[z1,z2,z8,z537,z3,z5,z6])],[(0,[z1,z2,z8,z538,z3,z5,z6]),(0,[z1,z2,z34,z8,z3,z5,z6]),(0,[z1,z17,z2,z3,z51,z5,z6]),(0,[z73,z1,z2,z8,z3,z69,z6])],[(0,[z1,z2,z8,z87,z5,z142,z6]),(0,[z539,z1,z2,z8,z3,z5,z6]),(0,[z33,z1,z2,z38,z3,z5,z6]),(0,[z1,z17,z2,z7,z3,z5,z6]),(0,[z1,z2,z540,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z11,z75]),(0,[z1,z2,z10,z38,z3,z5,z6]),(0,[z541,z1,z2,z8,z3,z5,z6])],[(0,[z542,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z543,z5,z6]),(1,[z1,z2,z238,z8,z3,z5]),(0,[z1,z2,z544,z8,z3,z5,z6])]],
   [[(1,[z1,z34,z8,z3,z5,z6]),(0,[z545,z1,z2,z8,z3,z5,z6]),(1,[z1,z17,z96,z3,z5,z6]),(0,[z1,z16,z2,z2,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z6,z465]),(0,[z73,z1,z2,z8,z96,z5,z6]),(0,[z73,z1,z2,z8,z3,z5,z77]),(0,[z1,z163,z2,z38,z3,z5,z6]),(0,[z546,z1,z2,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z547,z6]),(0,[z1,z16,z2,z49,z3,z5,z6]),(0,[z1,z179,z2,z8,z3,z5,z37]),(0,[z1,z2,z373,z38,z3,z5,z6]),(0,[z1,z2,z548,z8,z3,z5,z6])],[(1,[z1,z44,z8,z3,z5,z6]),(0,[z1,z2,z8,z549,z3,z5,z6]),(0,[z1,z2,z8,z5,z415,z6,z37]),(0,[z550,z1,z2,z8,z3,z5,z6]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z141,z3,z4,z5,z6]),(0,[z529,z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z8,z3,z551,z5,z6])],[(0,[z1,z17,z2,z3,z443,z5,z6]),(0,[z1,z16,z88,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z552]),(0,[z553,z1,z2,z8,z3,z5,z6])],[(0,[z554,z1,z2,z8,z3,z5,z6]),(0,[z1,z109,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z513,z3,z5,z6]),(0,[z1,z2,z8,z3,z555,z5,z6]),(0,[z1,z2,z8,z3,z5,z47,z6]),(0,[z1,z2,z38,z3,z5,z6,z94]),(0,[z1,z2,z3,z5,z472,z6,z94]),(0,[z1,z17,z2,z160,z3,z5,z6]),(0,[z1,z556,z2,z8,z3,z5,z6]),(1,[z1,z2,z3,z5,z503,z6])],[(0,[z1,z2,z8,z3,z5,z557,z6]),(0,[z1,z2,z8,z3,z5,z251,z6]),(0,[z1,z2,z8,z139,z3,z5,z6]),(0,[z33,z1,z2,z8,z3,z50,z6]),(0,[z209,z1,z2,z131,z8,z3,z5]),(0,[z1,z2,z8,z3,z5,z371,z6])],[(0,[z558,z1,z2,z8,z3,z5,z6]),(0,[z287,z1,z2,z58,z3,z5,z6]),(0,[z1,z2,z8,z54,z5,z142,z6]),(0,[z1,z17,z2,z3,z5,z6,z158]),(0,[z1,z2,z8,z3,z5,z6,z559])],[(0,[z1,z2,z8,z3,z560,z5,z6]),(1,[z1,z2,z3,z237,z5,z6]),(0,[z1,z2,z8,z3,z5,z561,z6]),(0,[z1,z2,z562,z8,z3,z5,z6]),(0,[z1,z2,z563,z8,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z75])]],
   [[(0,[z1,z2,z8,z3,z564,z5,z6]),(0,[z1,z2,z565,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z465])],[(0,[z566,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z567]),(0,[z1,z2,z92,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z568,z5,z6]),(0,[z1,z2,z569,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z570,z6]),(0,[z571,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z49,z3,z5,z6]),(0,[z1,z2,z48,z8,z3,z51,z5])],[(0,[z1,z2,z572,z8,z3,z5,z6]),(1,[z1,z136,z8,z3,z36,z6])],[(0,[z1,z2,z8,z3,z573,z5,z6]),(0,[z574,z1,z2,z8,z3,z5,z6]),(1,[z1,z2,z575,z3,z5,z6])],[(0,[z576,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z113,z6]),(0,[z1,z2,z8,z3,z5,z577,z6])],[(0,[z1,z2,z92,z61,z3,z5,z6]),(0,[z53,z1,z2,z3,z4,z5,z6]),(0,[z578,z1,z2,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z6,z579]),(0,[z287,z1,z2,z3,z5,z32,z6]),(0,[z1,z2,z8,z3,z5,z580,z6]),(0,[z1,z16,z2,z7,z3,z5,z6]),(0,[z1,z2,z8,z3,z581,z5,z6]),(0,[z1,z129,z8,z3,z4,z5,z6])],[(0,[z366,z1,z2,z8,z3,z5,z6]),(1,[z1,z2,z3,z314,z5,z6])]],
   [[(0,[z1,z2,z582,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z583,z5,z6]),(0,[z1,z2,z102,z8,z3,z5,z6]),(0,[z1,z584,z2,z8,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z6,z360]),(0,[z1,z2,z8,z3,z5,z6,z585])],[(0,[z1,z2,z61,z3,z5,z113,z6]),(0,[z85,z1,z2,z38,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z11,z6]),(0,[z586,z1,z2,z8,z3,z5,z6])],[(0,[z266,z1,z16,z2,z3,z5,z6]),(1,[z1,z2,z8,z119,z5,z6]),(0,[z1,z2,z38,z3,z137,z5,z6]),(0,[z1,z2,z38,z3,z35,z5,z6]),(0,[z1,z587,z2,z8,z3,z5,z6]),(0,[z1,z588,z2,z8,z3,z5,z6])],[(0,[z1,z589,z2,z8,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z1,z2,z8,z590,z3,z5,z6]),(0,[z1,z2,z8,z160,z35,z5,z6])],[(0,[z591,z1,z2,z8,z3,z5,z6]),(0,[z1,z592,z2,z8,z3,z5,z6]),(1,[z31,z2,z93,z3,z5,z6]),(0,[z1,z593,z2,z8,z3,z5,z6]),(0,[z1,z16,z2,z3,z87,z5,z6]),(0,[z1,z172,z17,z2,z3,z5,z6]),(0,[z1,z594,z2,z8,z3,z5,z6]),(0,[z1,z595,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z596]),(0,[z1,z2,z131,z8,z3,z5,z6])],[(0,[z53,z2,z42,z8,z3,z5,z6]),(0,[z53,z125,z2,z8,z3,z5,z6]),(0,[z53,z1,z17,z2,z3,z5,z6]),(0,[z1,z597,z17,z2,z3,z5,z6]),(1,[z1,z17,z9,z3,z5,z6]),(0,[z1,z2,z8,z3,z598,z5,z6]),(0,[z1,z2,z8,z3,z5,z599,z6])],[(0,[z1,z16,z2,z3,z5,z6,z158]),(0,[z1,z2,z600,z8,z3,z5,z6]),(0,[z1,z2,z601,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z6,z602]),(0,[z1,z2,z8,z3,z68,z5,z6]),(0,[z1,z603,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z604,z6])]],
   [[(1,[z1,z2,z513,z3,z5,z6]),(0,[z287,z1,z2,z84,z3,z5,z6]),(0,[z1,z2,z605,z8,z3,z5,z6]),(0,[z73,z1,z2,z486,z3,z5,z6]),(0,[z1,z2,z38,z3,z106,z5,z6])],[(0,[z1,z2,z8,z259,z3,z5,z6]),(1,[z1,z2,z139,z3,z5,z6]),(0,[z1,z2,z8,z3,z269,z5,z71]),(0,[z1,z2,z8,z606,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z11,z94]),(0,[z1,z17,z2,z3,z4,z5,z6]),(0,[z1,z607,z2,z8,z3,z5,z6]),(0,[z73,z162,z2,z8,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z70,z6]),(0,[z1,z608,z2,z8,z3,z5,z6])],[(0,[z287,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z609]),(0,[z1,z17,z2,z92,z3,z5,z6]),(1,[z1,z16,z2,z3,z5,z465]),(0,[z1,z2,z610,z8,z3,z5,z6]),(0,[z1,z2,z38,z96,z3,z5,z6]),(0,[z219,z1,z2,z3,z4,z5,z6]),(0,[z1,z587,z2,z38,z3,z5,z6]),(0,[z1,z611,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z612,z6])],[(0,[z1,z182,z19,z8,z3,z5,z6]),(1,[z1,z2,z145,z3,z5,z6]),(1,[z1,z2,z8,z3,z5,z409]),(0,[z1,z2,z8,z3,z5,z77,z6]),(0,[z1,z2,z3,z4,z313,z5,z6]),(0,[z1,z2,z8,z613,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z614]),(0,[z1,z2,z8,z615,z3,z5,z6])],[(0,[z1,z2,z8,z3,z87,z5,z6]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z131,z38,z3,z5,z6])],[(1,[z1,z616,z2,z3,z5,z6]),(0,[z1,z17,z2,z61,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z617,z6]),(0,[z1,z2,z8,z3,z618,z5,z6]),(0,[z1,z2,z8,z3,z619,z5,z6]),(0,[z1,z2,z620,z8,z3,z5,z6])],[(0,[z85,z53,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z621,z3,z5,z6]),(0,[z1,z2,z8,z3,z622,z5,z6]),(0,[z1,z2,z149,z8,z3,z5,z6]),(0,[z1,z2,z623,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z624,z6]),(0,[z1,z625,z2,z8,z3,z5,z6]),(0,[z1,z308,z16,z2,z3,z5,z6]),(0,[z1,z2,z96,z3,z4,z5,z6]),(0,[z1,z2,z92,z8,z3,z63,z6])]],
   [[(1,[z1,z2,z83,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z71,z6]),(0,[z45,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z626,z5,z6]),(0,[z1,z2,z8,z3,z627,z5,z6])],[(0,[z1,z2,z8,z3,z285,z6,z94]),(0,[z1,z17,z17,z2,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z11,z6]),(0,[z1,z628,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z629,z6])],[(0,[z1,z2,z3,z4,z5,z6,z94])],[(0,[z1,z630,z2,z8,z3,z5,z6]),(0,[z162,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z40,z3,z4,z5,z6]),(0,[z1,z2,z8,z631,z3,z5,z6])],[(1,[z266,z42,z8,z3,z5,z6]),(0,[z1,z111,z8,z3,z5,z11,z6]),(0,[z1,z2,z8,z3,z51,z5,z11]),(0,[z1,z2,z238,z8,z3,z5,z6]),(0,[z1,z2,z84,z8,z3,z5,z6]),(0,[z632,z1,z2,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z475,z5,z6]),(0,[z633,z1,z2,z8,z3,z5,z6]),(0,[z33,z1,z2,z131,z8,z3,z6]),(0,[z1,z17,z2,z528,z3,z5,z6]),(0,[z634,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z48,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z161,z5,z6])],[(0,[z635,z1,z2,z8,z3,z5,z6]),(0,[z31,z1,z2,z93,z3,z5,z6]),(0,[z0,z1,z2,z131,z8,z3,z5]),(0,[z1,z2,z8,z3,z5,z636,z6]),(0,[z1,z179,z2,z8,z3,z5,z6]),(1,[z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z38,z8,z4,z5,z6])],[(0,[z1,z17,z19,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z637]),(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z409]),(0,[z1,z182,z2,z8,z3,z5,z6]),(0,[z1,z2,z153,z8,z3,z5,z6])]],
   [[(0,[z1,z2,z8,z3,z5,z71,z6]),(0,[z45,z1,z17,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z340,z6])],[(1,[z1,z2,z8,z3,z269,z5]),(0,[z1,z2,z575,z8,z3,z5,z6]),(0,[z258,z1,z2,z3,z4,z5,z6])],[(0,[z1,z16,z2,z92,z3,z5,z6]),(1,[z1,z2,z486,z3,z5,z6]),(0,[z1,z2,z638,z8,z3,z5,z6]),(0,[z1,z111,z2,z8,z49,z3,z5]),(0,[z1,z2,z3,z4,z5,z347,z6]),(0,[z1,z2,z8,z3,z639,z5,z6])],[(0,[z266,z1,z19,z8,z3,z5,z6]),(0,[z1,z616,z2,z42,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z640,z6]),(0,[z1,z2,z8,z641,z3,z5,z6]),(0,[z1,z2,z8,z3,z642,z5,z6]),(0,[z1,z2,z215,z38,z3,z5,z6]),(0,[z1,z2,z187,z8,z3,z5,z6]),(0,[z643,z1,z2,z8,z3,z5,z6])],[(0,[z2,z93,z8,z61,z3,z5,z6]),(0,[z1,z2,z644,z8,z3,z5,z6]),(0,[z209,z1,z2,z8,z3,z51,z5]),(1,[z1,z129,z8,z3,z5,z6]),(0,[z1,z2,z84,z38,z3,z5,z6]),(0,[z1,z2,z8,z49,z5,z70,z6])],[(1,[z1,z2,z259,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z285,z6]),(0,[z209,z1,z2,z8,z3,z5,z47])],[(0,[z125,z1,z42,z8,z3,z5,z6]),(0,[z1,z597,z2,z8,z3,z5,z6]),(0,[z1,z17,z2,z215,z3,z5,z6]),(0,[z1,z2,z645,z8,z3,z5,z6]),(0,[z646,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z647,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z648,z6]),(0,[z209,z1,z17,z2,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z47,z6]),(0,[z73,z1,z16,z2,z3,z5,z6]),(0,[z649,z1,z2,z8,z3,z5,z6]),(0,[z1,z182,z2,z38,z3,z5,z6]),(1,[z1,z587,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z387,z6])]],
   [[(0,[z1,z650,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z651,z3,z5,z6]),(0,[z1,z2,z652,z8,z3,z5,z6]),(1,[z73,z1,z17,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z6,z127]),(0,[z1,z2,z3,z4,z137,z5,z6]),(0,[z1,z2,z58,z8,z3,z5,z11]),(0,[z1,z2,z8,z3,z5,z6,z653]),(0,[z1,z2,z3,z4,z35,z5,z6]),(0,[z654,z1,z2,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z655,z6]),(0,[z33,z2,z8,z3,z5,z71,z6]),(0,[z258,z1,z17,z2,z3,z5,z6]),(0,[z1,z16,z17,z2,z3,z5,z6]),(0,[z1,z2,z38,z3,z51,z5,z6])],[(1,[z1,z308,z2,z3,z5,z6]),(0,[z1,z16,z2,z656,z3,z5,z6]),(0,[z1,z594,z16,z2,z3,z5,z6]),(0,[z1,z2,z38,z7,z3,z5,z6]),(0,[z1,z2,z8,z657,z3,z5,z6]),(0,[z1,z2,z410,z8,z3,z5,z6]),(0,[z1,z2,z658,z8,z3,z5,z6])],[(0,[z1,z616,z2,z8,z3,z5,z6]),(0,[z1,z659,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z660,z6]),(0,[z1,z17,z2,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z661,z6])],[(0,[z31,z2,z93,z8,z3,z5,z6]),(0,[z662,z1,z2,z8,z3,z5,z6]),(0,[z1,z17,z2,z49,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z142,z6]),(0,[z1,z182,z8,z3,z137,z5,z6]),(0,[z1,z2,z8,z3,z5,z70,z37]),(0,[z1,z2,z84,z8,z3,z113,z6])],[(0,[z1,z16,z2,z93,z3,z5,z6]),(0,[z1,z2,z8,z663,z3,z5,z6])],[(0,[z1,z2,z8,z3,z3,z5,z6]),(1,[z1,z2,z8,z3,z5,z664]),(0,[z665,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z666,z5,z6]),(0,[z1,z17,z88,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z667,z6]),(0,[z1,z2,z3,z460,z5,z36,z6]),(1,[z1,z179,z8,z3,z5,z37]),(0,[z1,z111,z2,z8,z3,z5,z11]),(1,[z1,z2,z58,z3,z5,z127]),(0,[z1,z668,z2,z8,z3,z5,z6])],[(0,[z266,z1,z2,z8,z3,z5,z333]),(0,[z669,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z670,z8,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z113,z6]),(0,[z1,z607,z16,z2,z3,z5,z6]),(0,[z1,z2,z58,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z671,z5,z6]),(0,[z672,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z48,z202,z3,z5,z6])]],
   [[(0,[z85,z2,z8,z3,z87,z5,z6]),(0,[z1,z673,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z127])],[(0,[z1,z2,z8,z3,z5,z674,z6]),(1,[z33,z2,z8,z3,z71,z6]),(0,[z675,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z575,z3,z5,z6,z94]),(1,[z1,z2,z3,z161,z5,z6])],[(0,[z1,z19,z8,z3,z5,z36,z6]),(0,[z1,z2,z676,z8,z3,z5,z6]),(0,[z1,z16,z2,z3,z543,z5,z6]),(0,[z1,z2,z8,z656,z3,z5,z6]),(0,[z677,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z6,z158]),(0,[z1,z2,z8,z678,z3,z5,z6]),(0,[z679,z1,z2,z8,z3,z5,z6])],[(0,[z31,z1,z2,z8,z3,z5,z6]),(0,[z287,z1,z2,z3,z63,z5,z6]),(0,[z1,z16,z2,z54,z3,z5,z6]),(0,[z98,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z680]),(0,[z1,z2,z8,z3,z51,z5,z158])],[(0,[z1,z2,z681,z8,z3,z5,z6]),(0,[z1,z16,z2,z10,z3,z5,z6]),(1,[z226,z2,z8,z3,z5,z6]),(0,[z1,z136,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z142,z6])],[(0,[z1,z111,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z682,z5,z6])],[(0,[z1,z2,z8,z3,z5,z6,z683]),(0,[z1,z2,z8,z3,z5,z94,z37]),(0,[z1,z2,z8,z3,z5,z50,z94]),(0,[z1,z88,z2,z8,z5,z70,z6]),(0,[z1,z2,z153,z8,z5,z6,z37]),(0,[z1,z2,z684,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z685,z6]),(0,[z1,z2,z8,z3,z5,z6,z686]),(0,[z1,z2,z40,z8,z160,z5,z6])],[(0,[z266,z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z8,z687,z3,z5,z6]),(0,[z688,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z93,z3,z4,z5,z6]),(0,[z1,z2,z8,z689,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z47,z6]),(0,[z95,z1,z17,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z690])]],
   [[(0,[z1,z2,z8,z3,z5,z333,z6]),(0,[z691,z1,z2,z8,z3,z5,z6]),(0,[z692,z1,z2,z8,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z371,z6]),(0,[z1,z2,z8,z3,z5,z693,z6]),(0,[z1,z2,z8,z3,z5,z694,z6]),(0,[z1,z2,z8,z3,z5,z695,z6])],[(1,[z125,z19,z8,z3,z5,z6]),(0,[z53,z1,z2,z8,z3,z5,z664]),(0,[z1,z499,z2,z8,z3,z5,z6]),(1,[z1,z2,z131,z8,z3,z158])],[(0,[z1,z16,z2,z42,z3,z5,z6]),(0,[z1,z2,z696,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z664]),(0,[z1,z2,z240,z8,z3,z6,z94]),(0,[z1,z2,z8,z697,z3,z5,z6]),(0,[z1,z2,z8,z698,z3,z5,z6])],[(0,[z125,z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z54,z3,z5,z6]),(0,[z699,z1,z2,z8,z3,z5,z6]),(0,[z700,z1,z2,z8,z3,z5,z6])],[(0,[z287,z2,z8,z61,z3,z5,z6]),(0,[z1,z308,z2,z8,z3,z5,z6]),(0,[z701,z1,z2,z8,z3,z5,z6])],[(0,[z1,z2,z702,z8,z3,z5,z6]),(0,[z31,z1,z2,z58,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z114,z6]),(0,[z1,z16,z2,z3,z5,z6,z37]),(0,[z1,z2,z38,z3,z5,z11,z6]),(0,[z1,z2,z703,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z6,z704])],[(1,[z45,z2,z8,z3,z46,z6]),(0,[z1,z16,z2,z3,z5,z50,z6]),(0,[z1,z2,z3,z4,z5,z6,z242]),(0,[z1,z2,z38,z3,z479,z5,z6]),(0,[z1,z2,z684,z38,z3,z5,z6]),(0,[z1,z2,z705,z8,z3,z5,z6])],[(0,[z287,z1,z2,z38,z3,z5,z6]),(0,[z1,z17,z2,z3,z87,z5,z6]),(0,[z1,z16,z2,z3,z5,z113,z6]),(0,[z1,z2,z706,z8,z3,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z63,z173,z6]),(0,[z1,z2,z3,z5,z707,z6])],[(0,[z1,z2,z3,z4,z5,z708])],[(0,[z1,z17,z533,z3,z5,z6]),(0,[z1,z2,z3,z543,z113,z6]),(0,[z1,z2,z38,z3,z5,z409]),(0,[z1,z2,z3,z4,z5,z709])],[(0,[z53,z2,z54,z4,z5,z6]),(0,[z73,z1,z8,z106,z69,z6])],[(0,[z1,z2,z3,z710,z5,z6]),(0,[z1,z8,z3,z711,z5,z6]),(0,[z1,z2,z3,z712,z5,z6]),(1,[z1,z2,z8,z713,z6])],[(0,[z1,z2,z3,z4,z5,z251]),(0,[z1,z2,z8,z3,z5,z148]),(0,[z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z38,z238,z4,z5])],[(0,[z1,z2,z714,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z30]),(0,[z1,z2,z153,z8,z5,z6]),(0,[z73,z1,z8,z106,z5,z77]),(0,[z73,z1,z8,z711,z5,z6])],[(0,[z1,z607,z2,z3,z5,z465]),(0,[z1,z2,z115,z38,z3,z5]),(0,[z1,z129,z3,z63,z5,z6]),(0,[z1,z2,z8,z3,z715,z6])],[(0,[z1,z2,z716,z3,z5,z6]),(0,[z53,z2,z54,z237,z5,z6])],[(0,[z1,z2,z8,z3,z717,z6]),(0,[z1,z2,z8,z3,z718,z6]),(0,[z33,z2,z8,z152,z71,z6]),(0,[z1,z2,z152,z4,z5,z6]),(0,[z1,z2,z115,z3,z4,z5]),(0,[z1,z2,z719,z3,z5,z6])],[(0,[z1,z2,z8,z720,z5,z6]),(0,[z1,z2,z3,z68,z5,z6])],[(0,[z1,z721,z2,z3,z5,z6]),(0,[z1,z2,z119,z4,z5,z6]),(0,[z1,z2,z722,z3,z5,z6]),(0,[z1,z723,z2,z3,z5,z6]),(0,[z73,z1,z102,z106,z5,z6]),(0,[z1,z2,z724,z3,z5,z6]),(0,[z1,z2,z3,z5,z725,z6]),(0,[z1,z2,z4,z5,z6,z243]),(0,[z1,z587,z2,z3,z5,z726])],[(0,[z1,z2,z8,z3,z5,z727]),(0,[z1,z2,z3,z728,z5,z6]),(0,[z1,z16,z2,z49,z5,z70]),(0,[z1,z129,z3,z5,z36,z6]),(0,[z1,z2,z8,z3,z6,z729])],[(0,[z1,z2,z730,z3,z5,z6]),(0,[z1,z2,z731,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z251]),(0,[z1,z2,z8,z5,z732,z6]),(0,[z226,z2,z8,z3,z248,z6]),(0,[z1,z2,z3,z5,z733,z6]),(0,[z1,z2,z38,z517,z5,z6])],[(0,[z79,z2,z61,z3,z5,z6]),(0,[z1,z34,z145,z3,z5,z6]),(0,[z1,z16,z3,z5,z368,z6]),(0,[z1,z129,z210,z3,z4,z5])],[(0,[z1,z2,z734,z5,z415,z6]),(0,[z1,z2,z8,z35,z713,z6])]],
   [[(0,[z1,z2,z735,z3,z5,z6]),(0,[z1,z2,z38,z3,z269,z5]),(0,[z1,z2,z736,z3,z5,z6])],[(0,[z85,z2,z259,z87,z5,z6]),(0,[z1,z587,z163,z3,z5,z6]),(0,[z1,z17,z2,z3,z737,z6]),(0,[z1,z2,z238,z3,z5,z127])],[(0,[z1,z2,z238,z3,z5,z113])],[(0,[z1,z17,z286,z3,z5,z6]),(0,[z1,z2,z738,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z739]),(0,[z1,z2,z3,z5,z6,z740]),(0,[z1,z2,z741,z3,z5,z6]),(0,[z1,z2,z153,z38,z5,z6]),(0,[z1,z2,z202,z3,z5,z6]),(0,[z219,z1,z129,z3,z5,z6])],[(0,[z1,z2,z742,z3,z5,z6]),(0,[z1,z179,z8,z3,z5,z37])],[(0,[z1,z2,z743,z3,z5,z6]),(0,[z1,z2,z744,z3,z5,z6])],[(0,[z247,z1,z2,z3,z5,z371])],[(0,[z1,z2,z3,z745,z5,z6]),(0,[z1,z2,z746,z3,z5,z6]),(0,[z1,z2,z3,z161,z5,z6])],[(0,[z1,z2,z8,z3,z5,z747]),(0,[z1,z2,z8,z5,z6,z748])],[(0,[z1,z2,z361,z4,z5,z6]),(0,[z1,z17,z2,z3,z285,z6])],[(0,[z1,z129,z3,z5,z6,z94]),(0,[z1,z2,z8,z3,z5,z749]),(0,[z1,z2,z8,z3,z5,z750]),(0,[z1,z2,z3,z5,z751,z6]),(0,[z1,z2,z8,z3,z5,z752])],[(0,[z1,z2,z753,z8,z3,z5]),(0,[z1,z8,z711,z106,z5,z6]),(0,[z1,z2,z754,z3,z5,z6])],[(0,[z1,z179,z38,z3,z5,z37]),(0,[z1,z111,z129,z3,z5,z6])],[(0,[z53,z1,z129,z3,z5,z6]),(0,[z1,z17,z2,z3,z248,z6]),(0,[z1,z17,z2,z48,z5,z75])],[(0,[z1,z2,z8,z3,z5,z755]),(0,[z1,z2,z3,z4,z51,z50])]],
   [[(0,[z558,z2,z8,z87,z5,z6]),(0,[z1,z2,z3,z5,z756,z6]),(0,[z33,z2,z38,z3,z71,z6]),(0,[z1,z2,z8,z3,z5,z757]),(0,[z1,z457,z2,z48,z8,z5])],[(0,[z1,z129,z40,z3,z5,z6]),(0,[z1,z129,z3,z5,z340,z6]),(0,[z758,z2,z8,z3,z5,z6])],[(0,[z1,z2,z3,z759,z5,z6])],[(0,[z287,z1,z2,z3,z5,z371]),(0,[z1,z17,z190,z3,z5,z6]),(0,[z1,z129,z3,z5,z347,z6])],[(0,[z1,z760,z8,z3,z5,z6]),(0,[z1,z16,z129,z3,z5,z6])],[(0,[z1,z2,z761,z3,z5,z6]),(0,[z1,z2,z8,z3,z51,z449]),(0,[z1,z3,z228,z412,z5,z6]),(0,[z1,z2,z238,z3,z5,z347])],[(0,[z1,z2,z115,z102,z3,z5])],[(0,[z1,z2,z38,z411,z5,z6]),(0,[z1,z16,z2,z160,z35,z6]),(0,[z762,z2,z8,z3,z5,z6])],[(0,[z1,z8,z3,z5,z6,z763]),(0,[z162,z16,z2,z3,z5,z6])],[(0,[z1,z2,z8,z764,z3,z5]),(0,[z1,z765,z8,z3,z5,z6]),(0,[z81,z2,z8,z3,z5,z94]),(0,[z1,z17,z2,z3,z766,z6]),(0,[z1,z2,z3,z767,z5,z6]),(0,[z79,z1,z2,z238,z3,z5])],[(0,[z1,z2,z8,z3,z768,z6]),(0,[z1,z2,z8,z3,z5,z769]),(0,[z1,z2,z3,z5,z770,z127])],[(0,[z1,z2,z771,z3,z5,z6]),(0,[z125,z239,z8,z3,z5,z6])],[(0,[z33,z34,z8,z3,z71,z6]),(0,[z1,z2,z139,z152,z5,z6])],[(0,[z45,z2,z38,z3,z46,z6]),(0,[z1,z2,z273,z3,z69,z6]),(0,[z1,z2,z8,z3,z5,z772]),(0,[z1,z2,z3,z773,z5,z6]),(0,[z1,z179,z402,z3,z5,z37]),(0,[z1,z2,z210,z3,z5,z340])],[],[(0,[z1,z2,z8,z3,z774,z6]),(0,[z1,z2,z240,z38,z3,z6]),(0,[z1,z129,z3,z106,z5,z6])]],
   [[(0,[z1,z2,z3,z5,z775,z6]),(0,[z1,z2,z8,z3,z5,z776]),(0,[z662,z1,z17,z3,z5,z6]),(0,[z1,z8,z3,z5,z777,z6]),(0,[z1,z2,z273,z3,z5,z77]),(0,[z1,z2,z8,z713,z142,z6])],[(0,[z1,z2,z14,z8,z3,z5]),(0,[z1,z2,z240,z3,z4,z6]),(0,[z1,z308,z2,z3,z5,z708]),(0,[z1,z2,z8,z3,z69,z6]),(0,[z1,z129,z96,z3,z5,z6]),(0,[z778,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z729,z158])],[(0,[z1,z2,z416,z4,z5,z6]),(0,[z1,z16,z592,z3,z5,z6]),(0,[z31,z1,z2,z3,z5,z371]),(0,[z1,z17,z779,z3,z5,z6]),(0,[z1,z2,z780,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z781]),(0,[z1,z2,z4,z5,z505,z6]),(0,[z1,z2,z60,z49,z3,z5])],[(0,[z1,z136,z3,z460,z36,z6]),(0,[z1,z2,z10,z3,z5,z229])],[(0,[z1,z2,z8,z160,z21,z6]),(0,[z1,z2,z3,z782,z5,z6]),(0,[z1,z163,z96,z3,z5,z6]),(0,[z1,z17,z2,z255,z3,z5]),(0,[z1,z2,z783,z3,z5,z6])],[(0,[z178,z19,z8,z3,z5,z6]),(0,[z98,z1,z2,z3,z543,z6]),(0,[z1,z784,z8,z3,z5,z6]),(0,[z323,z1,z2,z131,z8,z3])],[(0,[z1,z2,z3,z5,z785,z664]),(0,[z1,z786,z129,z3,z5,z6])],[(0,[z1,z8,z3,z787,z36,z6])],[(0,[z0,z2,z8,z3,z5,z94]),(0,[z1,z308,z2,z3,z5,z371])],[(0,[z1,z2,z8,z3,z5,z307]),(0,[z1,z2,z153,z8,z5,z94]),(0,[z1,z17,z3,z5,z599,z6]),(0,[z1,z2,z38,z3,z69,z6]),(0,[z1,z2,z788,z3,z5,z6])],[(0,[z1,z44,z3,z4,z5,z6]),(0,[z1,z2,z108,z3,z5,z6]),(0,[z1,z2,z789,z3,z412,z5])],[(0,[z1,z111,z8,z3,z5,z11])],[(0,[z1,z2,z8,z3,z790,z6]),(0,[z1,z2,z8,z3,z5,z791]),(0,[z1,z2,z792,z3,z5,z6]),(0,[z1,z2,z575,z3,z5,z11]),(0,[z1,z2,z38,z3,z5,z77]),(0,[z1,z2,z115,z8,z3,z5]),(0,[z1,z2,z5,z503,z415,z6])],[],[(0,[z1,z2,z3,z793,z5,z6]),(0,[z1,z2,z3,z794,z5,z6]),(0,[z1,z2,z795,z3,z5,z6]),(0,[z1,z2,z8,z3,z796,z6]),(0,[z1,z2,z797,z3,z5,z288]),(1,[z1,z8,z3,z5,z798])],[(0,[z1,z2,z14,z38,z3,z5]),(0,[z1,z2,z3,z5,z27,z6]),(0,[z1,z16,z2,z3,z5,z799]),(0,[z162,z2,z8,z3,z248,z6]),(0,[z1,z129,z129,z3,z5,z6])]],
   [[(0,[z95,z296,z2,z3,z5,z6]),(1,[z1,z129,z238,z3,z5])],[(0,[z266,z17,z42,z3,z5,z6]),(0,[z1,z292,z17,z3,z5,z6]),(0,[z1,z2,z60,z3,z5,z37]),(0,[z1,z800,z2,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z801]),(0,[z1,z2,z3,z5,z6,z802]),(0,[z1,z88,z96,z412,z5,z6]),(0,[z1,z163,z129,z3,z5,z6])],[(0,[z1,z16,z2,z3,z5,z803]),(0,[z1,z111,z38,z3,z5,z11])],[(0,[z1,z2,z8,z3,z5,z133]),(0,[z1,z16,z2,z3,z5,z251]),(0,[z73,z1,z17,z3,z248,z6]),(0,[z1,z2,z779,z3,z5,z6]),(0,[z1,z2,z804,z8,z5,z6]),(0,[z1,z805,z129,z3,z5,z6]),(0,[z2,z3,z4,z5,z806,z6])],[(0,[z1,z2,z8,z3,z5,z6]),(0,[z1,z2,z807,z3,z5,z6]),(0,[z1,z129,z3,z29,z5,z6])],[(0,[z1,z2,z8,z3,z808,z6]),(0,[z1,z129,z9,z3,z5,z6]),(0,[z1,z8,z96,z711,z5,z6]),(0,[z1,z2,z809,z3,z5,z6]),(0,[z1,z2,z3,z51,z387,z50])],[(0,[z1,z2,z810,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z62])],[(0,[z1,z2,z811,z3,z5,z6]),(0,[z1,z2,z38,z238,z3,z5]),(0,[z1,z3,z4,z812,z5,z6])],[(0,[z1,z2,z8,z3,z5,z813]),(0,[z550,z2,z8,z3,z5,z47]),(0,[z1,z814,z3,z4,z5,z6]),(0,[z1,z2,z8,z160,z713,z6])],[(0,[z1,z2,z815,z3,z5,z6]),(0,[z1,z44,z8,z119,z5,z6]),(0,[z1,z2,z3,z816,z5,z6]),(0,[z1,z2,z3,z817,z5,z6]),(0,[z1,z2,z818,z3,z5,z6])],[(0,[z209,z2,z8,z3,z5,z819]),(0,[z1,z17,z3,z5,z6,z155]),(0,[z1,z2,z3,z4,z5,z371]),(0,[z1,z182,z129,z3,z5,z6]),(0,[z1,z2,z3,z5,z820,z6]),(0,[z1,z2,z58,z3,z5,z360])],[(0,[z1,z2,z38,z3,z5,z133]),(0,[z1,z2,z8,z3,z5,z821]),(0,[z1,z2,z58,z3,z5,z364])],[(0,[z1,z2,z38,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z822])],[(0,[z1,z823,z8,z3,z5,z6]),(0,[z1,z2,z476,z4,z5,z6]),(0,[z1,z88,z8,z5,z224,z6]),(0,[z1,z2,z160,z4,z35,z6])],[(1,[z2,z824,z3,z5,z6]),(0,[z1,z34,z139,z3,z5,z6]),(0,[z1,z16,z179,z3,z5,z37]),(0,[z1,z129,z160,z3,z5,z6])]],
   [[(0,[z266,z109,z42,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z148]),(0,[z1,z825,z129,z3,z5,z6])],[(0,[z1,z16,z2,z3,z285,z6]),(0,[z1,z2,z58,z3,z5,z375]),(0,[z1,z826,z2,z3,z5,z6]),(0,[z1,z129,z3,z5,z6,z158]),(0,[z1,z2,z238,z210,z3,z5])],[(0,[z1,z2,z8,z3,z5,z827]),(0,[z1,z2,z3,z4,z5,z288])],[(0,[z1,z2,z8,z3,z5,z828]),(0,[z1,z2,z829,z3,z5,z6]),(0,[z323,z2,z8,z3,z5,z94]),(0,[z1,z17,z2,z3,z5,z371]),(0,[z1,z2,z3,z4,z5,z409]),(0,[z1,z2,z40,z4,z142,z6])],[(0,[z1,z830,z44,z3,z5,z6]),(0,[z1,z163,z2,z528,z5,z6])],[(0,[z1,z16,z2,z3,z248,z6]),(0,[z1,z16,z2,z48,z5,z75]),(0,[z1,z2,z205,z68,z5,z6]),(0,[z1,z2,z831,z3,z5,z6]),(0,[z1,z2,z58,z210,z3,z5]),(0,[z1,z2,z38,z3,z5,z822])],[],[(0,[z0,z2,z240,z8,z3,z94]),(0,[z1,z2,z48,z8,z5,z349]),(0,[z1,z16,z534,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z832]),(0,[z1,z2,z8,z3,z833,z5]),(0,[z1,z2,z834,z3,z5,z6]),(0,[z1,z2,z835,z3,z5,z6]),(0,[z1,z2,z8,z3,z836,z6]),(0,[z1,z17,z696,z3,z5,z6]),(0,[z1,z2,z240,z8,z3,z307]),(0,[z1,z2,z837,z3,z4,z5]),(0,[z1,z2,z8,z5,z713,z6])],[(0,[z1,z2,z8,z3,z5,z838]),(0,[z1,z2,z3,z839,z5,z6]),(0,[z1,z2,z840,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z841])],[(0,[z1,z17,z2,z3,z5,z288]),(0,[z73,z1,z8,z106,z5,z6]),(0,[z1,z2,z842,z3,z5,z6])],[(0,[z1,z2,z843,z3,z5,z6]),(0,[z209,z2,z8,z3,z5,z47]),(0,[z1,z17,z2,z3,z5,z409]),(0,[z1,z292,z8,z3,z5,z11]),(0,[z1,z2,z38,z205,z5,z6]),(0,[z1,z2,z3,z5,z844,z6])],[(0,[z1,z2,z3,z845,z5,z6]),(0,[z1,z2,z846,z3,z5,z6]),(0,[z1,z2,z847,z3,z5,z6])],[(0,[z125,z17,z19,z3,z5,z6]),(0,[z1,z2,z14,z24,z3,z5]),(0,[z73,z1,z3,z443,z5,z6]),(0,[z1,z88,z2,z443,z5,z6]),(0,[z1,z17,z2,z131,z3,z158]),(0,[z1,z2,z402,z3,z5,z6]),(0,[z1,z2,z684,z3,z5,z360])],[(0,[z848,z16,z2,z3,z5,z6]),(0,[z1,z2,z849,z3,z5,z6])],[(0,[z1,z850,z44,z3,z5,z6]),(0,[z1,z264,z8,z3,z5,z11]),(0,[z1,z2,z3,z851,z5,z6]),(0,[z219,z2,z3,z126,z5,z6])]],
   [[(0,[z2,z8,z54,z720,z5,z6]),(0,[z1,z2,z852,z3,z5,z6]),(0,[z1,z129,z3,z5,z6,z853]),(0,[z1,z587,z405,z3,z5,z6])],[(0,[z1,z2,z139,z119,z5,z6]),(0,[z1,z2,z3,z4,z269,z5]),(0,[z1,z2,z8,z854,z3,z5]),(0,[z1,z2,z855,z8,z5,z6]),(0,[z1,z2,z8,z3,z787,z6])],[(0,[z53,z2,z8,z720,z5,z6]),(0,[z1,z308,z2,z3,z5,z781]),(0,[z73,z1,z38,z106,z5,z6]),(0,[z1,z2,z856,z3,z5,z6])],[(0,[z1,z2,z8,z857,z3,z6]),(0,[z1,z2,z8,z3,z5,z858]),(0,[z1,z2,z145,z119,z5,z6]),(0,[z1,z2,z3,z859,z5,z6]),(0,[z1,z2,z38,z25,z5,z6]),(0,[z1,z860,z8,z3,z5,z6]),(0,[z1,z861,z2,z3,z5,z6])],[(0,[z1,z2,z240,z8,z3,z6]),(0,[z1,z279,z2,z3,z354,z6]),(0,[z1,z16,z111,z3,z5,z11])],[(0,[z1,z2,z862,z3,z5,z6]),(0,[z1,z129,z92,z3,z5,z6])],[(0,[z95,z2,z93,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z752])],[(0,[z1,z863,z3,z4,z5,z6]),(0,[z1,z2,z864,z3,z5,z6])],[(0,[z85,z16,z2,z87,z5,z6]),(0,[z1,z2,z8,z3,z5,z865])],[(0,[z1,z17,z2,z3,z269,z5]),(0,[z1,z16,z2,z210,z3,z5])],[(1,[z73,z1,z443,z5,z6]),(0,[z1,z17,z2,z3,z51,z50]),(0,[z1,z2,z866,z3,z5,z6]),(0,[z1,z2,z3,z5,z867,z6]),(0,[z1,z2,z868,z8,z3,z5])],[(0,[z1,z136,z8,z3,z787,z6]),(0,[z1,z2,z49,z161,z5,z70])],[(0,[z1,z17,z2,z3,z869,z6]),(0,[z1,z870,z2,z3,z5,z6])],[(0,[z1,z2,z8,z152,z5,z307]),(0,[z33,z1,z129,z3,z5,z6])],[(0,[z1,z2,z8,z871,z5,z6]),(0,[z1,z2,z872,z3,z5,z6]),(0,[z1,z2,z3,z873,z5,z6]),(0,[z1,z179,z3,z4,z5,z37]),(0,[z1,z874,z2,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z875]),(0,[z1,z210,z3,z228,z4,z5])]],
   [[(0,[z1,z17,z44,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z876]),(0,[z1,z2,z217,z3,z5,z6]),(0,[z1,z8,z96,z25,z5,z6]),(0,[z1,z179,z3,z5,z503,z37])],[(0,[z33,z2,z3,z4,z71,z6])],[(0,[z1,z2,z171,z3,z5,z6]),(0,[z287,z223,z2,z3,z5,z6]),(0,[z1,z2,z877,z3,z5,z6]),(0,[z1,z2,z878,z3,z5,z6]),(0,[z1,z129,z3,z879,z5,z6])],[(0,[z1,z2,z8,z3,z5,z880]),(0,[z1,z2,z575,z49,z3,z5]),(0,[z1,z2,z881,z3,z5,z6])],[(0,[z53,z2,z8,z130,z5,z6]),(0,[z1,z457,z17,z3,z5,z6]),(0,[z1,z2,z8,z711,z5,z6])],[(0,[z1,z2,z8,z3,z5,z882]),(0,[z73,z1,z17,z5,z70,z6]),(0,[z1,z2,z883,z3,z5,z6])],[(0,[z1,z2,z884,z3,z5,z6]),(0,[z885,z2,z8,z3,z5,z6]),(0,[z1,z179,z2,z153,z8,z5])],[(0,[z1,z2,z886,z8,z5,z6]),(0,[z1,z2,z8,z3,z5,z887]),(0,[z1,z88,z8,z711,z5,z6])],[(0,[z266,z16,z42,z3,z5,z6]),(0,[z1,z128,z17,z3,z5,z6])],[(0,[z1,z2,z8,z152,z5,z6]),(0,[z33,z17,z2,z3,z71,z6]),(0,[z1,z129,z215,z3,z5,z6])],[(0,[z1,z2,z8,z888,z3,z5]),(0,[z1,z2,z889,z3,z5,z6]),(0,[z1,z129,z3,z5,z47,z6]),(0,[z1,z2,z8,z890,z3,z5]),(0,[z1,z198,z8,z3,z36,z6]),(0,[z1,z891,z2,z3,z5,z6])],[(0,[z1,z2,z892,z3,z5,z6]),(0,[z1,z16,z17,z3,z5,z465]),(0,[z1,z17,z2,z5,z415,z6]),(0,[z1,z2,z486,z3,z5,z409]),(0,[z1,z2,z590,z4,z5,z6]),(0,[z1,z2,z893,z3,z5,z6]),(0,[z1,z2,z894,z3,z5,z6])],[(0,[z1,z2,z895,z8,z5,z6]),(0,[z53,z2,z8,z54,z5,z6])],[(0,[z1,z896,z2,z3,z5,z6]),(0,[z1,z2,z897,z3,z5,z6]),(0,[z1,z38,z228,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z770])],[(0,[z45,z2,z3,z4,z46,z6]),(0,[z1,z2,z8,z3,z5,z898]),(0,[z1,z2,z66,z3,z5,z6])],[(0,[z85,z2,z87,z4,z5,z6]),(0,[z33,z2,z52,z8,z3,z6]),(0,[z1,z2,z84,z3,z114,z6]),(0,[z1,z2,z899,z3,z5,z6]),(0,[z900,z2,z8,z3,z5,z6])]],
   [[(0,[z31,z1,z2,z238,z3,z5])],[(0,[z1,z2,z38,z501,z5,z6]),(0,[z1,z2,z38,z152,z5,z6]),(0,[z33,z2,z8,z119,z71,z6]),(0,[z73,z1,z17,z3,z5,z409]),(0,[z901,z2,z8,z3,z5,z6]),(0,[z1,z2,z902,z3,z5,z6]),(0,[z1,z2,z903,z3,z5,z6]),(0,[z1,z129,z3,z5,z50,z6])],[(0,[z1,z2,z904,z3,z5,z6]),(0,[z1,z44,z8,z3,z5,z62]),(0,[z1,z2,z575,z3,z5,z37]),(0,[z1,z129,z3,z5,z113,z6])],[(0,[z1,z2,z3,z905,z5,z6]),(0,[z1,z2,z3,z906,z5,z6]),(0,[z0,z2,z38,z3,z5,z94]),(0,[z1,z16,z2,z3,z5,z708]),(0,[z1,z907,z2,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z908]),(0,[z53,z2,z38,z54,z5,z6]),(0,[z1,z909,z34,z3,z5,z6]),(0,[z1,z2,z152,z910,z5,z6]),(0,[z1,z2,z38,z3,z5,z307]),(0,[z1,z2,z8,z3,z5,z911]),(0,[z1,z2,z273,z3,z5,z6]),(0,[z1,z129,z2,z210,z3,z5]),(0,[z1,z2,z132,z3,z5,z6])],[(0,[z73,z1,z217,z106,z5,z6]),(0,[z1,z2,z3,z627,z5,z32])],[(0,[z45,z17,z2,z3,z46,z6]),(0,[z1,z2,z3,z5,z912,z288]),(0,[z1,z238,z3,z228,z4,z5])],[(0,[z1,z913,z2,z3,z5,z6]),(0,[z1,z2,z914,z3,z5,z6]),(0,[z1,z2,z3,z5,z915,z6]),(0,[z1,z2,z916,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z333]),(0,[z1,z2,z3,z917,z5,z6]),(0,[z1,z2,z918,z8,z3,z5]),(1,[z1,z129,z3,z5,z6]),(0,[z1,z2,z8,z3,z919,z6]),(0,[z1,z129,z38,z4,z5,z6]),(0,[z1,z2,z920,z3,z4,z5]),(0,[z1,z2,z38,z180,z5,z6])],[(1,[z2,z8,z720,z5,z6])],[(0,[z1,z2,z3,z4,z69,z6]),(0,[z1,z2,z921,z3,z4,z6])],[(0,[z1,z2,z8,z3,z5,z922]),(0,[z1,z2,z923,z3,z5,z6])],[(0,[z1,z2,z924,z3,z5,z6]),(0,[z1,z17,z2,z3,z925,z6])],[(0,[z226,z2,z8,z3,z5,z409]),(0,[z1,z2,z3,z4,z5,z77])],[(0,[z1,z2,z926,z8,z3,z5]),(0,[z1,z2,z927,z3,z5,z6]),(0,[z1,z2,z378,z160,z35,z6]),(0,[z1,z928,z2,z3,z5,z6])],[(0,[z125,z19,z513,z3,z5,z6])]],
   [[(0,[z1,z2,z929,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z333]),(0,[z1,z34,z8,z3,z5,z307])],[(0,[z1,z2,z930,z3,z5,z6]),(0,[z1,z2,z3,z931,z5,z6]),(0,[z1,z16,z2,z3,z5,z288]),(0,[z1,z2,z8,z49,z5,z429])],[(0,[z1,z2,z8,z3,z5,z932]),(0,[z1,z17,z2,z3,z933,z6]),(0,[z1,z2,z3,z5,z173,z371]),(0,[z1,z2,z8,z3,z713,z6]),(0,[z1,z2,z3,z5,z934,z6])],[(0,[z1,z2,z3,z5,z935,z6]),(0,[z1,z2,z8,z3,z5,z936]),(0,[z1,z937,z2,z3,z5,z6])],[(0,[z125,z16,z19,z3,z5,z6]),(0,[z1,z16,z2,z131,z3,z158]),(0,[z1,z111,z3,z4,z5,z11]),(0,[z1,z2,z92,z3,z63,z6])],[(0,[z1,z2,z14,z3,z325,z5]),(0,[z1,z17,z2,z3,z5,z77]),(0,[z938,z2,z8,z3,z5,z6])],[(0,[z1,z2,z939,z8,z3,z5]),(0,[z1,z2,z3,z940,z5,z6]),(0,[z1,z17,z2,z941,z5,z6]),(0,[z1,z16,z2,z3,z5,z942]),(0,[z943,z2,z8,z3,z5,z6]),(0,[z1,z238,z8,z3,z228,z5])],[(0,[z1,z2,z944,z3,z5,z6]),(0,[z1,z2,z153,z131,z8,z5]),(0,[z1,z2,z38,z3,z5,z821]),(0,[z1,z2,z3,z5,z945,z6])],[(0,[z649,z42,z8,z3,z5,z6]),(0,[z1,z946,z2,z3,z5,z6]),(0,[z1,z16,z7,z3,z5,z371]),(0,[z1,z2,z3,z947,z5,z6]),(0,[z1,z2,z149,z3,z159,z6])],[(0,[z287,z2,z61,z3,z5,z6]),(0,[z1,z2,z948,z3,z5,z6]),(0,[z73,z1,z273,z106,z5,z6]),(0,[z1,z2,z40,z38,z142,z6]),(0,[z1,z2,z3,z949,z5,z6])],[(0,[z1,z2,z950,z3,z5,z6]),(0,[z1,z2,z8,z49,z517,z5])],[(0,[z1,z2,z145,z3,z5,z62]),(0,[z1,z951,z2,z3,z5,z6]),(0,[z1,z129,z3,z475,z5,z6]),(0,[z1,z2,z10,z3,z161,z5])],[(0,[z1,z34,z8,z3,z5,z6]),(0,[z1,z2,z952,z8,z3,z5]),(0,[z953,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z954])],[(0,[z1,z2,z3,z4,z5,z133]),(0,[z1,z16,z2,z3,z5,z955])],[(0,[z1,z2,z956,z3,z5,z6]),(0,[z1,z129,z3,z5,z71,z6]),(0,[z1,z2,z957,z3,z412,z5]),(0,[z1,z2,z958,z3,z5,z6])],[(0,[z1,z2,z959,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z68,z5,z465]),(0,[z1,z16,z3,z5,z6,z704]),(0,[z1,z2,z153,z960,z5,z6]),(0,[z1,z961,z2,z3,z5,z6])],[(0,[z1,z962,z8,z3,z5,z6]),(0,[z1,z17,z2,z153,z5,z6]),(0,[z1,z963,z2,z3,z5,z6]),(0,[z1,z16,z2,z3,z51,z50]),(0,[z1,z2,z10,z3,z5,z371]),(0,[z1,z2,z3,z4,z5,z148]),(0,[z1,z2,z3,z5,z964,z6])],[(0,[z33,z2,z8,z3,z796,z6]),(0,[z1,z2,z656,z4,z5,z6]),(0,[z2,z8,z3,z5,z965,z6]),(0,[z1,z2,z678,z4,z5,z6])],[(1,[z760,z8,z3,z5,z6])],[(0,[z367,z379,z2,z3,z5,z6])],[(0,[z1,z966,z2,z3,z5,z6]),(0,[z967,z2,z8,z3,z5,z6]),(0,[z1,z2,z38,z262,z5,z6]),(0,[z1,z2,z8,z3,z50,z729])],[(0,[z1,z2,z968,z3,z5,z6]),(0,[z461,z2,z8,z3,z5,z94]),(0,[z209,z2,z38,z3,z5,z47]),(0,[z1,z779,z9,z3,z5,z6]),(0,[z1,z136,z8,z3,z36,z6])],[(0,[z1,z2,z969,z3,z5,z6]),(0,[z1,z2,z970,z3,z5,z6])],[(0,[z1,z2,z153,z8,z5,z47]),(0,[z1,z96,z3,z443,z5,z6]),(0,[z1,z2,z971,z3,z5,z6])],[(0,[z1,z17,z2,z3,z5,z148]),(0,[z1,z2,z60,z3,z5,z6]),(0,[z1,z2,z10,z3,z5,z32])],[(0,[z33,z2,z8,z3,z269,z71]),(0,[z1,z972,z2,z3,z5,z6]),(0,[z973,z2,z8,z3,z5,z6]),(0,[z1,z2,z107,z8,z142,z6]),(0,[z1,z2,z974,z3,z5,z6]),(0,[z1,z2,z890,z3,z4,z5])],[(0,[z1,z2,z3,z5,z32,z567]),(0,[z1,z2,z24,z3,z269,z5]),(0,[z1,z2,z238,z3,z4,z5]),(0,[z1,z2,z381,z3,z5,z6])],[(0,[z1,z16,z779,z3,z5,z6]),(0,[z1,z2,z975,z3,z5,z6]),(0,[z1,z2,z3,z976,z5,z6]),(0,[z1,z2,z977,z3,z5,z6])],[(0,[z1,z2,z3,z5,z978,z6])],[(0,[z1,z2,z3,z979,z5,z6]),(0,[z1,z16,z2,z255,z3,z5]),(0,[z1,z2,z980,z3,z5,z6]),(0,[z1,z129,z210,z3,z5,z6]),(0,[z1,z129,z3,z5,z6,z127])],[(0,[z1,z981,z2,z3,z5,z6]),(0,[z1,z2,z48,z8,z180,z5])]],
   [[(0,[z1,z2,z982,z3,z5,z6]),(0,[z1,z983,z2,z3,z5,z6])],[(0,[z1,z17,z34,z3,z5,z6]),(0,[z73,z1,z17,z443,z5,z6]),(0,[z1,z2,z3,z5,z715,z6])],[(0,[z1,z2,z3,z984,z5,z6]),(0,[z1,z2,z985,z3,z5,z6]),(0,[z1,z16,z2,z5,z415,z6]),(0,[z1,z2,z486,z3,z69,z6]),(0,[z1,z8,z3,z5,z11,z798]),(0,[z1,z129,z3,z5,z142,z6]),(0,[z1,z986,z8,z3,z5,z6])],[(0,[z1,z2,z987,z3,z5,z6]),(0,[z1,z2,z58,z3,z161,z5])],[(0,[z287,z1,z2,z238,z3,z5]),(0,[z1,z2,z8,z3,z5,z988]),(0,[z1,z2,z3,z5,z6,z989]),(0,[z1,z16,z2,z3,z5,z781]),(0,[z1,z2,z8,z3,z5,z990])],[(0,[z1,z2,z8,z3,z991,z5]),(0,[z1,z2,z8,z3,z5,z992]),(0,[z1,z17,z273,z3,z5,z6]),(0,[z1,z2,z486,z3,z5,z77]),(0,[z1,z2,z993,z3,z5,z6])],[(0,[z1,z2,z994,z8,z3,z5]),(0,[z1,z2,z995,z3,z5,z6])],[],[(0,[z1,z17,z2,z40,z142,z6]),(0,[z1,z2,z8,z3,z996,z6]),(0,[z1,z2,z997,z3,z5,z6]),(0,[z1,z2,z48,z4,z5,z75])],[(0,[z1,z129,z54,z3,z5,z6]),(0,[z33,z2,z8,z3,z71,z62]),(0,[z1,z16,z2,z3,z998,z6]),(0,[z1,z2,z215,z210,z4,z5]),(0,[z1,z2,z8,z3,z5,z999])],[(0,[z760,z42,z8,z3,z5,z6]),(0,[z1,z2,z353,z4,z5,z6]),(0,[z1,z438,z8,z3,z5,z37]),(0,[z1000,z2,z8,z3,z5,z6]),(0,[z1,z2,z1001,z3,z5,z6])],[(0,[z33,z2,z24,z3,z71,z6]),(0,[z73,z1,z17,z96,z5,z6]),(0,[z73,z1,z17,z3,z5,z77]),(0,[z1,z2,z920,z8,z3,z5])],[(0,[z1,z2,z1002,z3,z5,z6]),(0,[z1,z2,z8,z1003,z5,z6]),(0,[z1,z17,z193,z3,z5,z6]),(0,[z1,z2,z83,z3,z5,z6]),(0,[z1,z2,z1004,z8,z3,z5]),(0,[z1,z2,z3,z5,z1005,z6]),(0,[z1,z2,z8,z3,z5,z1006])],[(0,[z1,z2,z8,z3,z5,z1007]),(0,[z1,z2,z921,z8,z3,z6]),(0,[z1,z1008,z8,z3,z5,z6]),(1,[z2,z8,z3,z796,z6]),(0,[z1,z2,z10,z153,z8,z5]),(0,[z1,z129,z3,z5,z6,z75]),(0,[z1,z2,z1009,z3,z5,z6])],[],[(0,[z266,z42,z8,z3,z5,z133]),(0,[z1,z17,z2,z3,z5,z749]),(0,[z1,z2,z753,z3,z443,z5]),(0,[z162,z2,z8,z3,z5,z409]),(0,[z1,z3,z4,z5,z6,z1010])]],
   [[(0,[z266,z42,z8,z3,z5,z6]),(0,[z1,z129,z42,z3,z5,z6]),(0,[z1,z2,z8,z1011,z5,z6]),(0,[z1,z2,z3,z1012,z5,z6]),(0,[z1,z2,z3,z1013,z5,z6]),(0,[z1,z2,z734,z3,z5,z6]),(0,[z1,z2,z960,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1014,z6]),(0,[z1,z2,z240,z3,z472,z6]),(0,[z1,z2,z3,z4,z5,z865])],[(0,[z1,z2,z1015,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1016])],[(0,[z1,z129,z3,z39,z5,z6])],[(0,[z1,z2,z3,z1017,z5,z6]),(0,[z226,z2,z8,z3,z69,z6])],[(0,[z1,z2,z8,z3,z1018,z6]),(0,[z1,z2,z131,z8,z3,z729])],[(0,[z1,z16,z3,z156,z5,z6]),(0,[z73,z226,z8,z106,z5,z6])],[(0,[z211,z2,z61,z3,z5,z6]),(0,[z226,z2,z8,z3,z5,z77]),(0,[z1,z2,z3,z1019,z5,z6]),(0,[z2,z8,z3,z5,z806,z6])],[(0,[z1,z2,z8,z1020,z5,z6]),(0,[z1,z129,z8,z3,z5,z6])],[(0,[z1,z2,z1021,z3,z5,z6]),(0,[z1,z2,z259,z3,z5,z6]),(0,[z1,z2,z1022,z3,z5,z6]),(0,[z1,z2,z8,z5,z1023,z6]),(0,[z1,z2,z153,z8,z5,z70]),(0,[z1,z308,z2,z238,z3,z5]),(0,[z1,z2,z38,z3,z5,z898])],[(0,[z1,z2,z1024,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z1025]),(0,[z1,z2,z1026,z3,z5,z6]),(0,[z1,z2,z1027,z3,z5,z6]),(0,[z1,z2,z3,z443,z5,z6]),(0,[z1,z587,z2,z3,z5,z6]),(0,[z1,z481,z2,z48,z8,z5]),(0,[z1,z8,z3,z812,z5,z6]),(0,[z1,z1028,z2,z3,z5,z6])],[(0,[z1,z2,z1029,z3,z5,z6]),(0,[z1,z286,z8,z3,z5,z11])],[(0,[z1,z1030,z8,z3,z5,z6]),(0,[z1,z830,z2,z3,z5,z6]),(0,[z1,z2,z240,z8,z3,z158]),(0,[z1,z16,z2,z3,z5,z371]),(0,[z1,z2,z797,z3,z5,z6]),(0,[z1,z2,z3,z1031,z5,z6]),(0,[z1,z2,z1032,z3,z5,z6])],[(0,[z1,z308,z2,z3,z5,z6]),(0,[z1,z17,z2,z3,z768,z6]),(0,[z1,z7,z3,z412,z5,z6]),(0,[z1,z2,z40,z8,z142,z6])],[(0,[z1,z1033,z8,z3,z5,z6])]],
   [[(0,[z1,z34,z8,z152,z5,z6]),(0,[z1,z1034,z2,z3,z5,z6]),(0,[z1,z2,z8,z5,z6,z1035]),(0,[z1,z129,z38,z3,z5,z6])],[(0,[z1,z17,z548,z3,z5,z6]),(0,[z1,z784,z3,z4,z5,z6])],[(0,[z1,z16,z218,z3,z5,z6])],[(0,[z1,z2,z1036,z3,z5,z6]),(0,[z1,z16,z67,z3,z5,z6]),(0,[z1,z2,z1037,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1038]),(0,[z1,z2,z3,z715,z113,z6])],[(0,[z1,z2,z1039,z8,z3,z5]),(0,[z0,z2,z3,z4,z5,z94]),(0,[z1,z2,z854,z3,z443,z5]),(0,[z1,z2,z1040,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z307]),(0,[z1,z2,z8,z3,z5,z1041]),(0,[z1,z17,z2,z3,z69,z6]),(0,[z1,z16,z2,z3,z5,z409]),(0,[z1,z2,z8,z3,z1042,z6]),(0,[z1,z2,z1043,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z1044]),(0,[z1,z1045,z2,z3,z5,z6]),(0,[z1,z2,z1046,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1047]),(0,[z1,z16,z2,z3,z5,z1048])],[(0,[z1,z2,z8,z3,z5,z819]),(0,[z73,z1,z433,z8,z5,z6]),(0,[z1,z129,z3,z126,z5,z6])],[(0,[z1,z2,z8,z3,z1049,z6]),(0,[z1,z850,z2,z3,z5,z6]),(0,[z1,z16,z2,z153,z5,z6]),(0,[z1,z2,z1050,z3,z5,z6]),(0,[z1,z1051,z8,z3,z5,z6]),(0,[z1,z2,z428,z3,z479,z6])],[(0,[z45,z1,z129,z3,z5,z6]),(0,[z1,z530,z17,z3,z5,z6]),(0,[z1,z587,z7,z3,z5,z6]),(0,[z1,z2,z1052,z3,z5,z6]),(0,[z1,z2,z1053,z3,z5,z6])],[(0,[z0,z2,z8,z3,z5,z819])],[(0,[z1,z2,z3,z5,z1054,z6]),(0,[z85,z2,z86,z87,z5,z6]),(0,[z1,z2,z8,z3,z5,z465]),(0,[z73,z1,z486,z106,z5,z6]),(0,[z1,z2,z789,z8,z3,z5]),(0,[z1,z2,z153,z8,z5,z75])],[(0,[z1,z2,z139,z3,z5,z62]),(0,[z0,z17,z2,z3,z5,z94]),(0,[z1,z2,z8,z1055,z3,z5]),(0,[z1,z2,z3,z5,z6,z1056])],[(0,[z125,z19,z8,z3,z5,z6]),(0,[z1,z2,z3,z5,z1057,z6]),(0,[z1,z2,z3,z1058,z5,z6]),(0,[z1,z17,z2,z3,z5,z307]),(0,[z0,z2,z575,z3,z5,z94]),(0,[z1,z2,z3,z1059,z5,z6]),(0,[z367,z1,z2,z3,z5,z371]),(0,[z1,z2,z3,z5,z6,z1060]),(0,[z1,z179,z433,z8,z3,z5]),(0,[z225,z2,z154,z3,z5,z6])],[(0,[z1,z2,z8,z1061,z5,z6]),(0,[z1,z2,z8,z837,z3,z5]),(0,[z632,z2,z8,z54,z5,z6]),(0,[z1,z2,z238,z8,z3,z5]),(0,[z1,z8,z3,z1062,z5,z6])],[(0,[z1,z1063,z2,z3,z5,z6])]],
   [[(0,[z1,z16,z435,z3,z5,z6]),(0,[z1,z163,z2,z443,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z1064]),(0,[z1,z2,z3,z4,z5,z333]),(0,[z1,z2,z3,z5,z6,z1065]),(0,[z1,z2,z1066,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1067,z6])],[(0,[z1,z16,z2,z3,z269,z5]),(0,[z0,z2,z52,z8,z3,z5]),(0,[z1,z2,z3,z5,z503,z6]),(0,[z1,z16,z136,z3,z36,z6]),(0,[z1,z2,z38,z3,z5,z465])],[(0,[z1,z2,z240,z8,z49,z3]),(0,[z1,z17,z2,z238,z3,z5]),(0,[z1,z129,z84,z3,z5,z6])],[(0,[z1,z2,z8,z119,z5,z307])],[(0,[z1,z2,z3,z237,z5,z6]),(0,[z1,z2,z8,z3,z5,z1068]),(0,[z1,z17,z2,z310,z3,z5])],[(0,[z1,z34,z38,z3,z5,z6])],[(0,[z1,z17,z2,z3,z5,z133]),(0,[z1,z2,z24,z3,z5,z6]),(0,[z1,z16,z34,z3,z5,z6]),(0,[z1,z2,z8,z1069,z5,z6])],[(0,[z1,z17,z2,z3,z5,z6]),(0,[z1,z2,z3,z1070,z5,z6]),(0,[z1,z2,z1071,z3,z5,z6])],[(0,[z1,z2,z575,z3,z5,z6]),(0,[z1,z2,z8,z3,z1072,z6]),(0,[z1,z16,z44,z3,z5,z6]),(0,[z209,z2,z8,z3,z531,z5]),(0,[z1,z3,z4,z5,z1073,z6])],[],[(0,[z1,z2,z8,z3,z248,z409]),(0,[z1,z1074,z8,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1075,z6]),(0,[z1,z8,z210,z3,z228,z5]),(0,[z1,z2,z3,z5,z1076,z6])],[(0,[z1,z2,z1077,z8,z3,z6]),(0,[z1,z2,z3,z5,z6,z1078]),(0,[z1,z2,z8,z49,z5,z70])],[(0,[z1,z2,z10,z238,z3,z5])]],
   [[(0,[z1,z2,z8,z3,z5,z1079])],[(0,[z1,z2,z8,z119,z5,z6]),(0,[z1,z2,z1080,z3,z5,z6]),(0,[z1,z136,z38,z3,z36,z6]),(0,[z1,z129,z48,z3,z5,z6])],[(0,[z1,z1081,z2,z3,z5,z6]),(0,[z1,z2,z3,z39,z63,z6]),(0,[z1,z2,z92,z3,z480,z6])],[(0,[z31,z2,z93,z3,z5,z6]),(0,[z53,z2,z83,z54,z5,z6]),(0,[z33,z16,z2,z3,z71,z6]),(0,[z1,z2,z1082,z3,z5,z6]),(0,[z318,z499,z2,z3,z5,z6]),(0,[z1,z1083,z2,z3,z5,z6])],[(0,[z1,z17,z230,z3,z5,z6]),(0,[z1,z2,z8,z3,z51,z507])],[(0,[z1,z2,z1084,z8,z3,z5]),(0,[z1,z16,z2,z3,z1085,z6])],[(0,[z1,z2,z3,z5,z1086,z6]),(0,[z162,z2,z8,z3,z69,z6]),(0,[z1,z2,z38,z49,z5,z70])],[(0,[z209,z2,z3,z4,z5,z47]),(0,[z1,z2,z205,z976,z5,z6]),(0,[z1,z2,z3,z5,z30,z934])],[(0,[z1,z1087,z2,z3,z5,z6]),(0,[z1,z2,z115,z217,z3,z5])],[(0,[z1,z2,z38,z119,z5,z6]),(0,[z162,z2,z8,z3,z5,z77])],[(0,[z1,z2,z8,z3,z5,z1088]),(0,[z1,z962,z3,z4,z5,z6])],[(0,[z287,z2,z490,z3,z5,z6]),(0,[z73,z1,z17,z3,z69,z6]),(0,[z1,z1089,z2,z3,z5,z6]),(0,[z2,z8,z1090,z3,z5,z6])],[(0,[z1,z2,z38,z473,z5,z6]),(0,[z1,z17,z2,z3,z5,z832]),(0,[z1091,z2,z8,z3,z5,z6]),(0,[z1,z2,z3,z5,z1092,z6])],[(0,[z1,z199,z8,z3,z36,z6]),(0,[z1,z8,z3,z1093,z5,z6]),(0,[z1,z2,z295,z4,z5,z6])],[(0,[z1,z1094,z2,z3,z5,z6]),(0,[z1,z2,z48,z38,z5,z75])],[(0,[z1,z909,z2,z3,z5,z6]),(0,[z209,z17,z2,z3,z5,z47]),(0,[z234,z223,z2,z3,z5,z6]),(0,[z1,z308,z88,z96,z5,z6])]],
   [[(0,[z1,z1095,z8,z3,z5,z6]),(0,[z2,z824,z8,z3,z5,z6]),(0,[z45,z16,z2,z3,z46,z6]),(0,[z1,z2,z8,z5,z70,z748])],[(0,[z1,z2,z1096,z3,z5,z6]),(0,[z1,z2,z131,z8,z3,z15]),(0,[z1,z2,z645,z4,z5,z6]),(0,[z1,z308,z3,z228,z5,z6]),(0,[z1,z2,z3,z39,z313,z6]),(0,[z1,z2,z8,z3,z5,z1097])],[(0,[z1,z2,z38,z3,z5,z1088])],[(0,[z266,z42,z8,z3,z5,z333]),(0,[z1,z150,z2,z3,z5,z229])],[],[(0,[z1,z17,z2,z854,z3,z5])],[],[(0,[z1,z2,z1098,z3,z5,z6]),(0,[z1,z2,z1037,z152,z5,z6]),(0,[z1,z129,z273,z3,z5,z6]),(0,[z1,z2,z8,z3,z1099,z6])],[(0,[z1,z17,z652,z3,z5,z6])],[(0,[z1,z2,z1100,z3,z5,z6]),(0,[z53,z2,z8,z54,z5,z664]),(0,[z1,z2,z240,z8,z3,z50]),(0,[z1,z2,z486,z3,z5,z6]),(0,[z1,z2,z8,z160,z35,z6])],[(0,[z162,z2,z8,z3,z5,z6]),(0,[z125,z19,z171,z3,z5,z6]),(0,[z1,z2,z4,z5,z415,z6])],[(0,[z266,z42,z38,z3,z5,z6]),(0,[z1,z129,z19,z3,z5,z6]),(0,[z1,z2,z41,z3,z5,z6]),(0,[z219,z1,z2,z238,z3,z5])],[(0,[z1,z16,z2,z3,z69,z6]),(0,[z73,z162,z8,z106,z5,z6]),(1,[z1,z2,z8,z5,z748])],[(0,[z1,z2,z3,z5,z6,z1101])],[(0,[z45,z2,z8,z3,z796,z6])],[(0,[z31,z2,z3,z5,z99,z6]),(0,[z73,z1,z17,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z77])]],
   [[(0,[z287,z2,z154,z3,z5,z6]),(0,[z367,z2,z61,z3,z5,z6]),(0,[z1,z1102,z8,z3,z5,z6]),(0,[z1,z2,z8,z1103,z5,z6]),(1,[z1,z779,z3,z5,z6])],[(0,[z266,z616,z42,z3,z5,z6])],[(0,[z1,z129,z3,z5,z70,z6])],[(0,[z1,z1104,z2,z3,z5,z6])],[(0,[z1,z2,z1105,z3,z5,z6]),(0,[z1,z129,z3,z313,z5,z6])],[(0,[z1,z2,z8,z3,z5,z1106]),(0,[z1,z2,z8,z3,z5,z664]),(0,[z1,z2,z3,z5,z1107,z6]),(0,[z1,z2,z3,z5,z912,z6]),(0,[z1,z2,z1108,z8,z3,z5])],[(0,[z1,z2,z8,z1109,z5,z6]),(0,[z1,z2,z8,z1110,z5,z6]),(0,[z33,z2,z14,z8,z3,z71])],[(0,[z1,z1111,z2,z3,z5,z6]),(0,[z226,z2,z273,z3,z5,z6]),(0,[z1,z457,z8,z3,z5,z37])],[(0,[z1,z2,z3,z325,z269,z5]),(0,[z1,z198,z17,z3,z5,z6])],[],[(0,[z1,z2,z92,z3,z532,z6]),(0,[z1,z17,z88,z96,z5,z6]),(0,[z1,z2,z1112,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1113])],[(0,[z226,z2,z8,z3,z5,z6]),(0,[z1,z17,z656,z3,z5,z6]),(0,[z1,z16,z2,z238,z3,z5]),(0,[z900,z2,z3,z4,z5,z6])],[(0,[z1,z2,z48,z240,z8,z3]),(0,[z1,z17,z3,z228,z5,z6]),(0,[z1,z2,z3,z1114,z5,z6])],[(0,[z1,z2,z38,z3,z5,z664]),(0,[z1,z17,z2,z152,z5,z6]),(0,[z1,z16,z2,z310,z3,z5]),(0,[z1,z2,z8,z5,z70,z409]),(0,[z1,z2,z255,z3,z4,z5]),(0,[z1,z1115,z8,z3,z5,z6]),(1,[z1,z2,z8,z3,z729])],[(0,[z1,z1116,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1117,z6]),(0,[z1118,z2,z8,z3,z5,z6])],[(0,[z1,z16,z2,z3,z5,z133]),(0,[z1,z1119,z2,z3,z5,z6]),(0,[z1,z2,z10,z3,z5,z280]),(0,[z1,z2,z8,z3,z51,z629]),(0,[z1,z2,z1120,z3,z5,z6])]],
   [[(0,[z53,z17,z2,z54,z5,z6]),(0,[z1,z2,z38,z528,z5,z6])],[(0,[z1,z90,z17,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z799])],[(0,[z1,z2,z1121,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z1113])],[(0,[z1,z2,z8,z3,z1122,z6]),(0,[z1,z16,z2,z3,z5,z148]),(0,[z226,z2,z38,z3,z5,z6])],[(0,[z1,z2,z565,z3,z113,z6]),(0,[z1,z16,z116,z3,z5,z6]),(0,[z1,z2,z10,z3,z5,z321])],[(0,[z1,z2,z8,z3,z5,z1123]),(0,[z1,z2,z1124,z3,z5,z6]),(0,[z1,z2,z119,z1125,z5,z6]),(0,[z901,z17,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z803]),(0,[z1,z111,z2,z153,z8,z5])],[(0,[z1,z2,z8,z3,z5,z1126]),(0,[z529,z2,z93,z3,z5,z6]),(0,[z1,z2,z8,z3,z248,z77])],[(0,[z1,z2,z48,z8,z189,z5]),(0,[z1,z2,z66,z49,z5,z70])],[(0,[z125,z19,z38,z3,z5,z6]),(0,[z85,z1,z129,z3,z5,z6]),(0,[z1,z2,z3,z1127,z5,z6]),(0,[z33,z2,z3,z325,z71,z6]),(0,[z1,z17,z2,z3,z5,z911]),(0,[z1,z779,z8,z3,z5,z6]),(0,[z1,z2,z3,z5,z371,z321])],[(0,[z1,z2,z8,z1128,z5,z6]),(0,[z85,z2,z8,z720,z5,z6]),(0,[z1,z1129,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z62]),(0,[z1,z2,z8,z3,z5,z1130]),(0,[z1,z129,z3,z137,z5,z6]),(0,[z1,z129,z3,z35,z5,z6]),(0,[z1,z2,z8,z3,z5,z1131])],[(0,[z1,z2,z1132,z3,z5,z133]),(0,[z1,z1133,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1134]),(0,[z1,z2,z8,z3,z5,z1135]),(0,[z1,z8,z3,z5,z1073,z6]),(0,[z1,z2,z3,z1136,z5,z6])],[(0,[z1,z17,z3,z560,z5,z6]),(0,[z73,z1,z2,z68,z5,z6]),(0,[z1,z2,z3,z1137,z5,z6]),(0,[z1,z2,z8,z3,z5,z30])],[(0,[z1,z17,z2,z3,z5,z333]),(0,[z1,z2,z3,z472,z285,z6]),(0,[z1,z2,z10,z3,z5,z770])],[(0,[z1,z3,z4,z5,z1138,z6]),(0,[z1,z2,z3,z639,z113,z6])],[(0,[z1,z1139,z2,z3,z5,z6]),(0,[z1,z16,z7,z3,z5,z6]),(0,[z1,z1140,z129,z3,z5,z6]),(0,[z1,z129,z238,z3,z4,z5])],[(0,[z1,z2,z3,z5,z1141,z6]),(0,[z1,z2,z8,z1142,z5,z6]),(0,[z1,z2,z8,z3,z5,z798])]],
   [[(0,[z1,z2,z1143,z3,z5,z6])],[(0,[z1,z1144,z2,z3,z5,z6]),(0,[z1,z2,z8,z1145,z5,z6]),(0,[z1,z2,z38,z3,z5,z62]),(0,[z2,z8,z3,z5,z47,z819]),(0,[z1,z2,z1146,z3,z5,z6]),(0,[z1,z1051,z3,z4,z5,z6])],[(0,[z1,z16,z2,z40,z142,z6]),(0,[z2,z8,z3,z5,z6,z1147]),(0,[z79,z1,z129,z3,z5,z6])],[(0,[z1,z1148,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z285,z6]),(0,[z1,z2,z38,z3,z5,z30]),(0,[z1,z2,z48,z8,z5,z75])],[(0,[z1,z2,z3,z5,z1149,z6]),(0,[z1,z594,z2,z3,z173,z6]),(0,[z1,z2,z3,z4,z5,z465]),(0,[z1,z2,z3,z5,z1150,z6]),(0,[z1,z2,z49,z4,z5,z70])],[(0,[z1,z2,z141,z3,z347,z6])],[(0,[z1,z2,z3,z5,z503,z465]),(0,[z1,z530,z8,z3,z5,z11]),(0,[z1,z129,z2,z238,z3,z5])],[],[(0,[z1,z34,z3,z4,z5,z6]),(0,[z1,z17,z187,z3,z5,z6]),(0,[z1,z2,z3,z5,z1151,z6]),(0,[z1,z2,z3,z1152,z5,z6]),(0,[z1,z2,z976,z4,z5,z6]),(0,[z1,z2,z1153,z3,z4,z5])],[(0,[z1,z1154,z2,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z750]),(0,[z73,z1,z2,z115,z8,z5]),(0,[z1,z2,z1155,z3,z5,z6])],[(0,[z1,z2,z38,z536,z5,z6])],[(0,[z1,z109,z2,z3,z5,z6]),(0,[z1,z129,z2,z3,z5,z6]),(0,[z1,z2,z1156,z3,z5,z6])],[(0,[z287,z2,z395,z3,z5,z6]),(0,[z1,z2,z58,z3,z5,z321])],[],[(0,[z1,z16,z2,z3,z5,z858])],[(0,[z1,z2,z10,z3,z5,z503]),(0,[z1,z2,z38,z12,z5,z6])]],
   [[(0,[z1,z2,z1157,z3,z5,z6]),(0,[z848,z2,z8,z3,z5,z6]),(1,[z1,z8,z711,z5,z6]),(0,[z73,z1,z8,z255,z106,z5])],[(0,[z287,z2,z824,z3,z5,z6]),(0,[z1,z17,z357,z3,z5,z6]),(0,[z1,z2,z102,z255,z3,z5]),(0,[z79,z2,z3,z475,z5,z6])],[(0,[z1,z1158,z8,z3,z5,z6]),(0,[z1,z136,z3,z4,z36,z6]),(0,[z1,z8,z3,z5,z6,z1010])],[(0,[z2,z8,z720,z87,z5,z6])],[(0,[z1,z2,z58,z3,z5,z770])],[],[(0,[z1,z2,z3,z5,z6,z1159]),(1,[z1,z2,z3,z715,z6]),(0,[z1,z2,z3,z63,z715,z6])],[(0,[z1,z2,z8,z3,z5,z1160]),(0,[z1,z2,z8,z1161,z3,z5])],[(0,[z1,z34,z8,z119,z5,z6]),(0,[z1,z1162,z8,z3,z5,z6]),(0,[z1,z129,z3,z51,z5,z6]),(0,[z1,z2,z3,z1163,z5,z6])],[(0,[z1,z129,z7,z3,z5,z6]),(0,[z162,z2,z273,z3,z5,z6])],[(0,[z85,z2,z8,z87,z5,z6]),(0,[z1,z2,z48,z575,z3,z5]),(1,[z1,z2,z976,z5,z6]),(0,[z1,z129,z141,z3,z5,z6])],[(0,[z571,z2,z8,z3,z5,z47]),(0,[z1,z2,z8,z210,z3,z5])],[(0,[z1,z2,z92,z3,z5,z371]),(0,[z73,z1,z8,z106,z248,z6]),(0,[z1,z3,z228,z4,z5,z6]),(0,[z1,z2,z3,z5,z32,z770])],[(0,[z2,z8,z3,z5,z796,z6]),(0,[z1,z2,z3,z1164,z5,z6]),(0,[z2,z8,z3,z5,z819,z6]),(0,[z1,z2,z3,z5,z1165,z6]),(0,[z1,z179,z17,z3,z5,z37])],[(0,[z1,z129,z3,z443,z5,z6]),(0,[z73,z1,z129,z3,z5,z6]),(0,[z73,z1,z16,z106,z5,z6])],[(0,[z1,z16,z17,z3,z5,z371]),(0,[z1,z2,z3,z1166,z5,z6])]],
   [[(0,[z1,z2,z84,z3,z489,z6]),(0,[z31,z2,z824,z3,z5,z6]),(0,[z1,z587,z88,z3,z5,z6]),(0,[z1,z2,z1167,z8,z3,z5]),(0,[z1,z2,z3,z4,z5,z988]),(0,[z1,z2,z3,z5,z1168,z6]),(0,[z1,z2,z10,z132,z3,z5]),(0,[z1,z2,z3,z1169,z5,z6])],[(0,[z1,z44,z139,z3,z5,z6]),(0,[z1,z16,z88,z96,z5,z6]),(0,[z1,z129,z3,z5,z1170,z6]),(0,[z1,z2,z1171,z3,z5,z6])],[(0,[z85,z2,z38,z87,z5,z6])],[(0,[z1,z1172,z8,z3,z5,z6]),(0,[z1,z44,z145,z3,z5,z6]),(0,[z1,z16,z3,z228,z5,z6]),(0,[z1,z2,z38,z210,z4,z5]),(0,[z1,z2,z8,z3,z5,z729])],[(0,[z1,z1173,z2,z3,z5,z6]),(0,[z1,z16,z2,z152,z5,z6]),(0,[z1,z2,z1174,z3,z5,z6]),(0,[z1,z2,z3,z790,z4,z6]),(0,[z1,z2,z38,z160,z35,z6])],[(0,[z1,z2,z3,z325,z5,z6]),(0,[z1,z2,z215,z443,z5,z6]),(0,[z162,z2,z38,z3,z5,z6]),(0,[z1,z1175,z8,z3,z5,z6])],[(0,[z1,z2,z1176,z3,z5,z6]),(0,[z0,z16,z2,z3,z5,z94]),(0,[z1,z2,z1177,z3,z5,z6]),(0,[z1,z2,z1178,z8,z3,z5])],[(0,[z1,z2,z8,z3,z1179,z5]),(0,[z53,z16,z2,z54,z5,z6]),(0,[z1,z16,z2,z3,z5,z307]),(0,[z1,z1180,z8,z3,z5,z6]),(0,[z1,z2,z58,z3,z5,z503]),(0,[z1,z3,z1093,z4,z5,z6])],[(0,[z1,z7,z779,z3,z5,z6]),(0,[z1,z2,z40,z8,z30,z142]),(0,[z1,z2,z1181,z3,z5,z6])],[],[(0,[z1,z2,z8,z3,z5,z1182]),(0,[z1,z2,z3,z5,z6,z1183])],[(0,[z1,z111,z410,z3,z5,z11]),(0,[z1,z2,z160,z314,z35,z6])],[(0,[z266,z42,z3,z4,z5,z6]),(0,[z1,z2,z3,z910,z5,z6]),(0,[z1,z129,z3,z5,z11,z6])],[(0,[z1,z2,z8,z152,z5,z62])],[(0,[z1,z2,z8,z3,z1184,z6])],[(0,[z1,z2,z8,z1185,z5,z6]),(0,[z98,z1,z2,z3,z5,z371]),(0,[z1,z2,z238,z3,z5,z242])]],
   [[(0,[z1,z17,z3,z5,z224,z6])],[(0,[z1,z2,z1186,z3,z5,z6]),(0,[z1,z2,z1187,z3,z5,z6]),(0,[z1,z129,z238,z8,z3,z5])],[(0,[z1,z17,z462,z3,z5,z6]),(0,[z1188,z2,z8,z3,z5,z6]),(0,[z1,z2,z3,z1189,z5,z6]),(0,[z1,z2,z3,z1190,z5,z6])],[(0,[z1,z16,z2,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z333]),(0,[z1,z16,z2,z3,z919,z6])],[(0,[z1,z2,z1191,z3,z5,z6]),(0,[z1,z308,z2,z3,z5,z465]),(0,[z1,z2,z1192,z3,z5,z6]),(0,[z1,z179,z8,z5,z415,z37]),(0,[z1,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z770,z6])],[(0,[z1,z2,z410,z3,z5,z6])],[(0,[z1,z2,z8,z5,z1193,z6]),(0,[z1,z2,z8,z3,z1194,z5]),(0,[z1,z2,z3,z5,z785,z6]),(0,[z1,z17,z697,z3,z5,z6]),(0,[z1,z1195,z129,z3,z5,z6])],[(0,[z1,z2,z92,z3,z354,z6]),(0,[z1,z179,z8,z3,z5,z798]),(0,[z1,z2,z3,z4,z5,z1025])],[(0,[z1,z129,z61,z3,z5,z6]),(0,[z1,z2,z58,z132,z3,z5]),(0,[z1,z2,z3,z1196,z5,z6])],[(0,[z1,z2,z1197,z8,z3,z6]),(0,[z1,z2,z8,z3,z5,z251]),(0,[z1,z1198,z8,z3,z5,z6]),(0,[z0,z2,z8,z3,z285,z94]),(0,[z1,z2,z3,z5,z113,z371]),(0,[z1,z88,z96,z4,z5,z6])],[(0,[z209,z1,z2,z240,z8,z3]),(0,[z1,z17,z2,z115,z3,z5]),(0,[z1,z111,z3,z5,z11,z321])],[(0,[z1,z2,z215,z4,z5,z6]),(0,[z1,z2,z215,z238,z4,z5]),(0,[z1,z2,z1153,z8,z3,z5])],[(0,[z1,z2,z1199,z3,z5,z6]),(0,[z1,z1200,z34,z3,z5,z6]),(0,[z1,z2,z238,z3,z39,z5])],[(0,[z1,z2,z1201,z3,z5,z6]),(0,[z1,z2,z1202,z3,z5,z6]),(0,[z1,z2,z8,z3,z737,z6]),(0,[z1,z8,z3,z5,z1138,z6]),(0,[z1,z2,z310,z38,z3,z5])],[(0,[z1,z2,z1132,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z664]),(0,[z1,z2,z956,z3,z5,z664]),(0,[z1,z2,z1203,z8,z3,z5]),(0,[z1,z129,z3,z228,z5,z6]),(0,[z1,z2,z38,z389,z5,z6])],[(0,[z73,z1,z17,z48,z5,z6]),(0,[z1,z163,z88,z96,z5,z6]),(0,[z1,z2,z310,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z1204,z5,z6]),(0,[z1,z2,z1205,z3,z5,z6]),(0,[z541,z2,z8,z3,z5,z47]),(0,[z1,z16,z174,z3,z5,z6])],[(0,[z1,z2,z38,z3,z5,z251]),(0,[z33,z44,z8,z3,z71,z6]),(0,[z943,z16,z2,z3,z5,z6]),(0,[z1,z2,z153,z971,z5,z6]),(0,[z1,z2,z84,z3,z113,z6])],[(0,[z1,z2,z8,z3,z5,z1206])],[(0,[z1,z611,z17,z3,z5,z6]),(0,[z1,z111,z17,z3,z5,z11]),(0,[z1,z2,z8,z663,z35,z6])],[(0,[z1,z2,z1207,z3,z5,z6]),(0,[z1,z2,z3,z68,z5,z371]),(0,[z226,z2,z3,z4,z5,z6])],[(0,[z1,z1208,z2,z3,z5,z6]),(0,[z1,z1209,z2,z3,z5,z6])],[(0,[z1,z1210,z8,z3,z5,z6])],[(0,[z2,z8,z3,z796,z71,z6])],[(0,[z1,z2,z8,z3,z5,z942]),(0,[z1,z2,z153,z8,z5,z409]),(0,[z1,z2,z40,z41,z142,z6])],[(0,[z1,z2,z8,z1211,z5,z6]),(0,[z125,z19,z3,z4,z5,z6]),(0,[z1,z1212,z2,z3,z5,z6]),(0,[z45,z2,z8,z3,z124,z6]),(0,[z209,z16,z2,z3,z5,z47]),(0,[z1,z278,z2,z3,z114,z6]),(0,[z73,z1,z8,z443,z5,z6]),(0,[z1,z2,z215,z976,z5,z6])],[(0,[z1,z17,z2,z3,z5,z1047]),(0,[z1,z2,z8,z3,z248,z6]),(0,[z1,z2,z8,z957,z3,z5]),(0,[z1,z668,z8,z3,z5,z37]),(0,[z1,z2,z38,z3,z5,z1206])],[(0,[z1,z88,z110,z96,z5,z6])],[(0,[z1,z1213,z2,z3,z5,z6]),(0,[z1,z2,z1214,z3,z5,z6])],[(0,[z209,z1,z129,z3,z5,z6])],[(0,[z1,z2,z38,z3,z285,z6])],[(0,[z1,z2,z8,z3,z5,z955]),(0,[z1,z1215,z2,z3,z5,z6]),(0,[z33,z1,z2,z14,z8,z3]),(0,[z1,z17,z2,z3,z5,z465]),(0,[z1,z129,z49,z3,z5,z6])]],
   [[(0,[z1,z34,z8,z3,z5,z62]),(0,[z2,z8,z3,z5,z819,z94]),(0,[z258,z1,z129,z3,z5,z6])],[(0,[z19,z760,z8,z3,z5,z6]),(0,[z1,z2,z1216,z3,z5,z6]),(0,[z1,z163,z2,z3,z5,z6]),(0,[z1,z96,z3,z1217,z5,z6]),(0,[z1,z1218,z2,z3,z5,z6])],[(0,[z1,z2,z38,z3,z248,z6]),(0,[z2,z8,z3,z5,z6,z1219])],[(0,[z1,z2,z1220,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1221]),(0,[z1,z16,z350,z3,z5,z6]),(0,[z1,z136,z129,z3,z5,z6]),(0,[z1,z2,z3,z1222,z5,z6])],[(0,[z1,z2,z3,z4,z5,z30]),(0,[z1,z2,z1223,z3,z5,z6])],[(0,[z1,z2,z8,z3,z766,z6]),(0,[z1,z2,z8,z3,z869,z6]),(0,[z125,z760,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z726]),(0,[z1,z2,z8,z3,z5,z1224])],[(0,[z2,z93,z824,z3,z5,z6]),(0,[z427,z1,z129,z3,z5,z6])],[(0,[z1,z2,z1225,z3,z5,z6]),(0,[z1,z2,z1226,z8,z3,z5]),(0,[z1,z2,z378,z3,z5,z6])],[(0,[z33,z2,z139,z3,z71,z6]),(0,[z1,z2,z362,z3,z5,z6]),(0,[z1,z2,z38,z392,z5,z6]),(0,[z73,z1,z102,z3,z5,z6])],[(0,[z1,z2,z1227,z3,z5,z6]),(0,[z1,z2,z1228,z3,z5,z6])],[(0,[z1,z2,z3,z1229,z5,z6]),(0,[z33,z2,z145,z3,z71,z6]),(0,[z427,z1,z17,z3,z5,z6]),(0,[z1,z2,z131,z8,z3,z604])],[(0,[z1,z2,z8,z3,z50,z307]),(0,[z1,z2,z8,z3,z5,z1230]),(0,[z1,z2,z3,z1231,z5,z6]),(0,[z1,z2,z8,z1232,z3,z5]),(0,[z1,z2,z153,z4,z5,z6]),(0,[z1,z2,z210,z3,z4,z5])],[(0,[z1,z17,z3,z342,z5,z6])],[(0,[z1,z2,z824,z3,z5,z6]),(0,[z1,z2,z87,z443,z5,z6]),(0,[z1,z2,z1233,z3,z5,z6]),(0,[z1,z2,z153,z5,z503,z6]),(0,[z1,z2,z38,z3,z5,z726])],[(0,[z1,z1234,z8,z3,z5,z6]),(0,[z1,z2,z3,z5,z371,z465]),(1,[z1,z129,z210,z3,z5])],[(0,[z1,z2,z3,z460,z5,z6])]],
   [[(0,[z1,z17,z2,z240,z3,z6]),(0,[z1,z587,z17,z3,z5,z6]),(0,[z1,z2,z8,z255,z3,z5]),(0,[z1235,z1,z129,z3,z5,z6])],[(0,[z1,z1236,z2,z3,z5,z6]),(0,[z1,z2,z1237,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1238]),(0,[z1239,z2,z8,z3,z5,z6])],[(0,[z1,z129,z3,z87,z5,z6]),(0,[z1,z44,z8,z3,z5,z307]),(0,[z73,z1,z17,z106,z5,z6]),(0,[z1,z17,z2,z49,z5,z70]),(0,[z1,z129,z1240,z3,z5,z6]),(0,[z1,z2,z977,z3,z5,z30])],[(0,[z1,z2,z8,z3,z50,z359]),(0,[z1,z16,z2,z3,z5,z882])],[(0,[z1,z2,z8,z1241,z5,z6]),(0,[z1,z2,z8,z3,z1242,z6]),(0,[z885,z16,z2,z3,z5,z6]),(0,[z1,z2,z8,z5,z415,z6])],[(0,[z1,z2,z54,z443,z5,z6]),(0,[z1,z17,z2,z119,z5,z6]),(0,[z1,z172,z2,z3,z5,z280]),(0,[z1,z2,z3,z5,z6,z321]),(0,[z1,z16,z516,z3,z5,z6]),(0,[z1,z2,z1243,z3,z5,z6])],[(0,[z662,z42,z8,z3,z5,z6]),(0,[z2,z8,z3,z720,z5,z6]),(0,[z1,z17,z239,z3,z5,z6]),(0,[z1,z2,z38,z210,z3,z5]),(0,[z1,z2,z92,z3,z479,z6])],[(0,[z1,z2,z8,z3,z1244,z5]),(0,[z1,z8,z3,z228,z5,z6]),(0,[z1,z129,z3,z5,z32,z6])],[(0,[z1,z7,z273,z3,z5,z6]),(0,[z1,z2,z38,z255,z3,z5]),(0,[z1,z2,z1245,z3,z5,z6])],[(0,[z1,z2,z38,z231,z5,z6]),(0,[z1,z2,z3,z5,z1246,z6]),(1,[z2,z8,z3,z5,z819]),(0,[z1,z2,z1247,z3,z5,z6])],[(0,[z1,z2,z1248,z3,z5,z6]),(0,[z1,z2,z8,z5,z748,z75])],[],[(0,[z226,z2,z486,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1249]),(0,[z1,z1250,z2,z3,z5,z6])],[(0,[z1,z2,z1251,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1252]),(0,[z1,z1253,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1097]),(0,[z529,z2,z373,z3,z5,z6]),(0,[z1,z2,z3,z5,z1254,z6])],[(0,[z1,z44,z8,z3,z5,z6])],[(0,[z1,z1255,z2,z3,z5,z6])]],
   [[(0,[z2,z824,z61,z3,z5,z6]),(0,[z53,z2,z8,z54,z5,z251]),(0,[z1091,z17,z2,z3,z5,z6]),(0,[z1,z587,z2,z3,z5,z1113])],[(0,[z1,z2,z1256,z3,z5,z6]),(0,[z1,z16,z2,z115,z3,z5])],[(0,[z1,z2,z8,z3,z5,z1257]),(0,[z1,z2,z58,z3,z5,z465]),(0,[z1,z2,z5,z1150,z415,z6]),(0,[z1,z2,z310,z8,z3,z5])],[(0,[z366,z1,z2,z443,z5,z6]),(0,[z1,z2,z8,z3,z69,z409])],[(0,[z1,z1200,z2,z3,z5,z6]),(0,[z1,z2,z3,z1217,z5,z6]),(0,[z1,z2,z92,z3,z715,z6])],[(0,[z1,z2,z8,z3,z925,z6])],[(0,[z1,z17,z705,z3,z5,z6]),(0,[z427,z1,z2,z68,z5,z6]),(0,[z162,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z3,z5,z1258])],[(0,[z1,z2,z8,z3,z5,z1259]),(0,[z1,z17,z625,z3,z5,z6]),(0,[z1,z1260,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1261]),(0,[z1,z308,z2,z656,z5,z6]),(0,[z1,z1262,z2,z3,z5,z6]),(0,[z1,z2,z238,z132,z3,z5])],[(0,[z1,z2,z8,z3,z5,z1263]),(0,[z1,z2,z58,z3,z5,z579]),(0,[z1,z17,z3,z412,z5,z6]),(0,[z1,z2,z8,z3,z5,z708])],[(0,[z1,z8,z3,z5,z798,z37]),(0,[z1,z2,z3,z5,z1264,z6]),(0,[z1,z2,z8,z3,z5,z709]),(0,[z1,z2,z3,z1265,z5,z6])],[(0,[z1,z2,z190,z4,z5,z6]),(0,[z1,z2,z3,z5,z32,z465]),(0,[z1,z2,z4,z5,z147,z6]),(0,[z1,z2,z131,z3,z4,z158]),(0,[z1,z2,z151,z4,z5,z6])],[(0,[z1,z2,z145,z3,z5,z307]),(0,[z1,z2,z131,z8,z3,z307]),(0,[z1266,z2,z8,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1267]),(0,[z1,z2,z3,z314,z5,z6]),(0,[z1,z1268,z2,z3,z5,z6]),(0,[z1,z2,z48,z60,z3,z5])],[(0,[z1,z2,z1269,z3,z5,z6]),(0,[z1,z2,z402,z5,z415,z6]),(0,[z1,z215,z228,z4,z5,z6]),(0,[z1,z129,z3,z3,z5,z6]),(0,[z1,z2,z38,z365,z5,z6])],[(0,[z125,z1,z129,z3,z5,z6]),(0,[z31,z499,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1270,z6]),(0,[z1,z2,z240,z575,z3,z6]),(0,[z1,z17,z628,z3,z5,z6]),(0,[z1,z17,z2,z160,z35,z6]),(0,[z1,z2,z1271,z3,z5,z6])],[(0,[z1,z2,z8,z1272,z5,z6]),(0,[z1,z2,z1273,z3,z5,z6]),(0,[z1,z16,z2,z3,z5,z1038]),(0,[z1,z2,z1274,z3,z5,z6])],[(0,[z1,z2,z3,z1275,z5,z6]),(0,[z1,z2,z8,z3,z5,z371]),(0,[z1,z308,z2,z68,z5,z6]),(0,[z1,z129,z131,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z5,z6,z1276])],[(0,[z1,z17,z9,z3,z5,z6]),(0,[z1,z179,z129,z3,z5,z6])],[(0,[z634,z2,z93,z3,z5,z6]),(0,[z73,z1,z106,z4,z5,z6])],[(0,[z1,z2,z8,z3,z5,z1277]),(0,[z1,z129,z93,z3,z5,z6]),(0,[z442,z1,z2,z131,z8,z3]),(0,[z1,z2,z48,z8,z5,z748])],[(0,[z1,z2,z513,z3,z5,z6]),(0,[z266,z760,z8,z3,z5,z6]),(0,[z1,z1278,z2,z3,z5,z6])],[(0,[z1,z2,z8,z3,z1279,z6]),(0,[z1,z2,z3,z1280,z5,z6])],[(0,[z1,z2,z8,z3,z1281,z6]),(0,[z0,z1,z2,z240,z8,z3]),(0,[z1,z2,z240,z8,z3,z11]),(0,[z1,z16,z2,z3,z5,z465]),(0,[z1,z2,z8,z3,z5,z288]),(0,[z1,z2,z153,z58,z8,z5])],[(0,[z1,z2,z145,z3,z5,z6]),(0,[z1,z2,z38,z3,z5,z371]),(0,[z1,z2,z8,z3,z5,z409]),(0,[z1,z8,z3,z5,z787,z6]),(0,[z1,z2,z1282,z3,z4,z5])],[(0,[z1,z2,z8,z3,z5,z1283]),(0,[z1,z17,z2,z753,z3,z5]),(0,[z1,z2,z8,z3,z5,z1048])],[(0,[z1,z616,z2,z3,z5,z6]),(0,[z1,z17,z2,z3,z5,z664]),(0,[z1,z2,z273,z3,z248,z6]),(0,[z1,z2,z1284,z3,z5,z6]),(0,[z1,z1115,z3,z4,z5,z6])],[(0,[z1,z17,z2,z1109,z5,z6]),(0,[z1,z2,z3,z412,z5,z6]),(0,[z953,z16,z2,z3,z5,z6]),(0,[z1,z129,z10,z3,z5,z6])],[(0,[z318,z1,z2,z3,z5,z371]),(0,[z1,z2,z217,z255,z3,z5]),(0,[z1,z2,z3,z5,z6,z1285])],[(0,[z1,z2,z1286,z3,z5,z6]),(0,[z1,z2,z3,z1287,z5,z6]),(1,[z1,z2,z3,z5,z770])],[(0,[z287,z1,z129,z3,z5,z6]),(0,[z1,z17,z2,z14,z3,z5]),(0,[z1,z2,z1288,z3,z5,z6])],[(0,[z1,z2,z8,z49,z5,z177]),(0,[z73,z226,z17,z3,z5,z6]),(0,[z1,z2,z3,z5,z371,z127]),(0,[z1,z2,z38,z3,z5,z288])],[(0,[z1,z2,z8,z1289,z5,z6]),(0,[z226,z17,z2,z3,z5,z6]),(0,[z1,z587,z3,z106,z5,z6]),(0,[z1,z2,z3,z5,z6,z1290]),(0,[z1,z2,z153,z402,z5,z6])]],
   [[(0,[z1,z2,z1291,z8,z3,z5]),(0,[z1,z1292,z8,z3,z5,z6]),(0,[z1,z1293,z2,z3,z5,z6]),(0,[z1,z129,z88,z3,z5,z6])],[(0,[z1,z2,z97,z4,z5,z6]),(0,[z1,z1294,z2,z3,z5,z6]),(0,[z1,z2,z3,z63,z674,z6]),(0,[z73,z162,z17,z3,z5,z6]),(0,[z1,z2,z40,z381,z142,z6])],[(0,[z1,z2,z8,z3,z5,z1295]),(0,[z1,z2,z8,z1296,z5,z6]),(0,[z1,z2,z1297,z3,z5,z6])],[(0,[z1,z129,z3,z5,z6,z37]),(0,[z1,z2,z8,z49,z5,z748])],[(0,[z1,z593,z17,z3,z5,z6]),(0,[z1,z16,z7,z3,z5,z465]),(0,[z1,z90,z8,z3,z5,z37])],[(0,[z1,z2,z8,z1298,z3,z5]),(0,[z1,z1299,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z62]),(0,[z1,z2,z8,z3,z269,z5]),(0,[z2,z8,z3,z46,z796,z6]),(0,[z1,z16,z191,z3,z5,z6])],[(0,[z1,z2,z1300,z3,z5,z6]),(0,[z1,z2,z8,z3,z51,z50])],[(0,[z1,z16,z2,z240,z3,z6]),(0,[z1,z2,z3,z1301,z5,z6])],[(0,[z1,z2,z8,z976,z5,z6])],[(0,[z1,z2,z8,z3,z5,z1302]),(0,[z33,z2,z8,z3,z71,z307]),(0,[z0,z1,z129,z3,z5,z6]),(0,[z1,z1303,z2,z3,z5,z6]),(0,[z1,z17,z569,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1304])],[(0,[z1,z1305,z2,z3,z5,z6]),(0,[z1,z2,z1306,z3,z5,z6]),(0,[z1,z2,z1187,z119,z5,z6]),(0,[z0,z2,z3,z5,z472,z94]),(0,[z1,z2,z40,z310,z8,z142])],[(0,[z1,z863,z8,z3,z5,z6]),(0,[z1,z1307,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1308]),(0,[z1,z2,z3,z5,z387,z6]),(0,[z1309,z2,z8,z3,z5,z6])],[(0,[z1,z2,z8,z3,z5,z876]),(0,[z31,z1,z129,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1310]),(0,[z1,z16,z2,z119,z5,z6]),(0,[z1,z2,z3,z1311,z5,z6]),(0,[z1,z2,z110,z3,z5,z6]),(0,[z73,z1,z8,z106,z5,z409])],[(0,[z1,z17,z2,z3,z5,z62]),(0,[z1,z17,z2,z3,z5,z1130])],[(0,[z162,z2,z486,z3,z5,z6]),(0,[z1,z8,z3,z5,z798,z6]),(0,[z1,z129,z238,z3,z5,z6]),(0,[z1,z129,z8,z210,z3,z5]),(0,[z1,z2,z38,z3,z51,z50])],[(0,[z1,z1312,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z285,z6]),(0,[z1,z17,z2,z3,z5,z30]),(0,[z1313,z2,z8,z3,z5,z6]),(0,[z1,z2,z3,z1314,z5,z6])]],
   [[(0,[z1,z2,z1315,z3,z5,z6]),(0,[z1,z2,z48,z8,z5,z409]),(0,[z1,z163,z187,z3,z5,z6]),(0,[z1,z2,z38,z976,z5,z6])],[(0,[z1,z2,z8,z1316,z5,z6]),(0,[z1,z182,z17,z3,z137,z6]),(0,[z1,z2,z8,z5,z70,z450]),(0,[z1,z2,z138,z4,z5,z6])],[(0,[z1,z44,z8,z152,z5,z6]),(0,[z1,z597,z2,z3,z5,z375]),(0,[z1,z1317,z2,z3,z5,z6]),(0,[z1,z308,z129,z3,z5,z6]),(0,[z1,z129,z58,z3,z5,z6]),(0,[z1,z2,z210,z3,z161,z5]),(0,[z1,z2,z84,z3,z159,z6]),(0,[z1,z2,z58,z3,z5,z127])],[(0,[z1,z1318,z8,z3,z5,z6]),(0,[z73,z1,z163,z3,z5,z6]),(0,[z1,z2,z3,z4,z248,z6]),(0,[z1,z111,z8,z3,z5,z798]),(0,[z1,z129,z3,z5,z1319,z6])],[(0,[z31,z2,z3,z126,z5,z6]),(0,[z1,z2,z3,z1320,z5,z6]),(0,[z1,z308,z2,z210,z3,z5])],[(0,[z216,z2,z8,z87,z5,z6]),(0,[z33,z2,z8,z3,z71,z6]),(0,[z1,z2,z8,z119,z5,z62]),(0,[z1,z17,z3,z1217,z5,z6]),(0,[z1,z102,z96,z3,z5,z6]),(0,[z1,z1321,z8,z3,z5,z6])],[(0,[z1,z2,z1322,z3,z5,z6]),(0,[z1,z2,z86,z3,z5,z6]),(0,[z1,z1323,z2,z3,z5,z6]),(0,[z1,z179,z153,z8,z5,z37])],[(0,[z1,z2,z3,z5,z472,z6]),(0,[z1,z2,z8,z3,z1085,z6]),(0,[z1,z2,z141,z3,z113,z6])],[(0,[z1,z2,z575,z3,z285,z6]),(0,[z1,z2,z1324,z3,z5,z6])],[(0,[z1,z2,z1325,z3,z5,z6]),(0,[z1,z2,z3,z1326,z5,z6]),(0,[z1,z2,z1327,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z781]),(0,[z1,z2,z3,z5,z1328,z6])],[(0,[z1,z2,z1329,z3,z5,z6])],[(0,[z1,z16,z2,z3,z5,z1007]),(0,[z1,z2,z40,z8,z713,z6])],[(0,[z266,z1,z129,z3,z5,z6]),(0,[z1,z2,z1330,z3,z5,z6]),(0,[z1,z1331,z8,z3,z5,z6]),(0,[z1,z2,z3,z1332,z5,z6])],[(0,[z2,z760,z8,z3,z5,z6]),(0,[z1,z2,z68,z4,z5,z6]),(0,[z1,z2,z8,z3,z69,z77]),(0,[z1,z2,z92,z238,z3,z5]),(0,[z1,z2,z8,z3,z5,z748]),(0,[z1,z2,z131,z8,z3,z158])],[(0,[z1,z2,z3,z5,z1333,z133]),(0,[z1,z2,z8,z3,z998,z6]),(0,[z1,z2,z582,z4,z5,z6]),(0,[z1,z17,z538,z3,z5,z6]),(0,[z1,z136,z17,z3,z36,z6]),(0,[z1,z1334,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z1335]),(0,[z1,z1158,z3,z4,z5,z6]),(0,[z1,z2,z1336,z3,z5,z6])],[(0,[z1,z2,z3,z5,z1333,z6]),(0,[z1,z2,z1337,z3,z5,z6]),(0,[z1,z17,z96,z3,z5,z6]),(0,[z1,z88,z2,z68,z5,z6]),(0,[z1,z2,z38,z5,z415,z6])]],
   [[(0,[z1,z1338,z2,z3,z5,z6]),(0,[z1,z2,z131,z8,z3,z456]),(0,[z1,z2,z210,z3,z5,z32]),(0,[z1,z2,z84,z3,z715,z6])],[(0,[z1,z1339,z8,z3,z5,z6])],[(0,[z45,z2,z8,z3,z46,z6]),(0,[z1,z2,z1340,z3,z5,z6]),(0,[z73,z1,z17,z528,z5,z6]),(0,[z1,z2,z48,z202,z5,z75])],[(0,[z1,z2,z1341,z3,z5,z6])],[(0,[z1,z2,z1342,z3,z5,z6]),(0,[z1,z16,z3,z5,z249,z6]),(0,[z1,z2,z1343,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z1344])],[(0,[z1,z2,z1345,z3,z5,z6]),(0,[z1,z2,z8,z3,z6,z1346]),(0,[z1,z16,z17,z3,z5,z6]),(0,[z1,z2,z3,z5,z1347,z6])],[],[(0,[z1,z2,z8,z3,z393,z50]),(0,[z1,z1348,z2,z3,z5,z6]),(0,[z1,z2,z60,z3,z51,z50])],[],[(0,[z1,z2,z1349,z3,z5,z6]),(0,[z1,z44,z38,z3,z5,z6]),(0,[z1,z2,z3,z1350,z5,z6]),(0,[z1,z2,z1351,z3,z5,z6]),(0,[z1,z2,z1352,z3,z5,z6]),(0,[z1,z136,z362,z3,z36,z6])],[(0,[z1,z2,z1282,z8,z3,z5]),(0,[z1,z129,z3,z46,z5,z6]),(0,[z1,z2,z1353,z3,z5,z6]),(0,[z1,z2,z153,z8,z51,z5]),(0,[z1,z2,z8,z452,z5,z70])],[(0,[z1,z2,z145,z152,z5,z6]),(0,[z45,z1,z2,z14,z8,z3]),(0,[z1,z2,z1354,z3,z5,z6]),(0,[z1,z2,z131,z38,z3,z158])],[(0,[z1,z2,z1355,z3,z5,z6]),(0,[z1,z2,z1356,z3,z5,z6]),(0,[z1,z2,z1357,z8,z3,z6]),(0,[z1,z2,z139,z3,z5,z307]),(0,[z73,z1,z2,z443,z5,z6]),(0,[z73,z1,z115,z8,z106,z5]),(0,[z1,z2,z8,z3,z51,z729])],[(0,[z1,z2,z8,z3,z1358,z6]),(0,[z31,z2,z3,z671,z5,z6]),(0,[z1,z17,z129,z3,z5,z6]),(0,[z1,z88,z2,z115,z8,z5]),(0,[z1,z2,z1359,z3,z5,z6])],[(0,[z1,z2,z1360,z3,z5,z6]),(0,[z85,z17,z2,z87,z5,z6]),(0,[z1,z2,z8,z3,z933,z6]),(0,[z1,z1361,z2,z3,z5,z6]),(0,[z1,z129,z215,z4,z5,z6])],[(0,[z1,z2,z1362,z3,z5,z6]),(0,[z1,z608,z17,z3,z5,z6]),(0,[z1,z2,z38,z443,z5,z6]),(0,[z1,z17,z2,z210,z3,z5])]],
   [[(0,[z1,z16,z2,z3,z5,z664]),(0,[z1,z814,z8,z3,z5,z6]),(0,[z1,z2,z38,z444,z5,z6])],[(0,[z1,z2,z519,z4,z5,z6]),(0,[z162,z17,z2,z3,z5,z6]),(0,[z1,z2,z8,z3,z5,z77]),(0,[z1,z111,z8,z615,z3,z5])],[(0,[z1,z2,z8,z941,z5,z6]),(0,[z1,z2,z3,z1363,z5,z6])],[(0,[z1,z2,z1364,z8,z3,z6]),(0,[z1,z2,z1365,z3,z5,z6]),(0,[z1,z2,z48,z8,z521,z5])],[(0,[z1,z16,z2,z14,z3,z5]),(0,[z1,z88,z8,z96,z5,z6])],[],[(0,[z1,z2,z302,z8,z142,z6]),(0,[z1,z2,z3,z1366,z5,z6]),(0,[z1,z2,z102,z3,z5,z6]),(0,[z226,z16,z2,z3,z5,z6]),(0,[z1,z2,z273,z3,z5,z409]),(0,[z1,z38,z3,z228,z5,z6]),(0,[z1,z1367,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1368,z5,z6]),(0,[z1,z129,z205,z3,z5,z6])],[(0,[z1,z2,z1369,z3,z5,z6]),(0,[z1,z2,z139,z3,z5,z6]),(0,[z1,z1370,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1371,z5,z6]),(0,[z1,z2,z8,z3,z1372,z6]),(0,[z1373,z1,z129,z3,z5,z6])],[(0,[z1,z2,z8,z3,z1374,z6]),(0,[z1,z2,z8,z49,z525,z5])],[(0,[z1,z2,z3,z1125,z5,z6]),(0,[z1,z2,z1375,z3,z5,z6]),(0,[z1,z2,z486,z3,z248,z6]),(0,[z1,z2,z60,z3,z5,z11]),(0,[z1,z1376,z2,z3,z5,z6])],[(0,[z1,z2,z240,z8,z3,z37]),(0,[z1,z88,z38,z96,z5,z6]),(0,[z1,z2,z8,z1377,z5,z6]),(0,[z1,z2,z1378,z3,z5,z6]),(0,[z1,z129,z3,z5,z6,z242]),(0,[z1,z2,z48,z132,z5,z75]),(0,[z1,z2,z1379,z3,z5,z6])],[(0,[z1,z1380,z8,z3,z5,z6]),(0,[z1,z2,z3,z5,z1381,z6])],[(0,[z1,z2,z8,z1382,z5,z6]),(0,[z1,z2,z14,z3,z4,z5]),(0,[z1,z16,z2,z3,z1122,z6]),(0,[z1383,z2,z8,z3,z5,z6])],[(0,[z1,z2,z4,z5,z206,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 504) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 504).take 502) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1006).take 400) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1406)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [504, 502, 400] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 113).take 130).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 243).take 141).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 384).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 505).take 7).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [113, 130, 141, 121, 7] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_38577

theorem PEqualNP.Outside.L_meta_38577 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 4209044160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38577.solve