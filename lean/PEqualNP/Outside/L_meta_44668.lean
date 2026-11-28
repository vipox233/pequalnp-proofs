import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_44668

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
  Nat.testBit (4276812992 * 2 ^ 32 + 4243105920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x62b63184406cdba0#64 ++ 0x9062b63184406cdb#64 ++ 0xe7f6318440ffffdc#64 ++ 0xb0e7f6318440ffff#64 : BitVec 256),
   (0x098816b81b162dc0#64 ++ 0x41098816b81b162d#64 ++ 0x19883ff87f1e3fbd#64 ++ 0xd319883ff87f1e3f#64 : BitVec 256),
   (0x160ac15985a34600#64 ++ 0x24160ac15985a346#64 ++ 0x1e0fc1ff87e3c77e#64 ++ 0xfc1e0fc1ff87e3c7#64 : BitVec 256),
   (0xe00d6a0ee803b001#64 ++ 0x0ae00d6a0ee803b0#64 ++ 0xe00ffe0ff803f8fb#64 ++ 0xefe00ffe0ff803f8#64 : BitVec 256),
   (0xbd50000776d80002#64 ++ 0x0fbd50000776d800#64 ++ 0xfff0000ffffc00ff#64 ++ 0x7ffff0000ffffc00#64 : BitVec 256),
   (0xdfe7bde000000004#64 ++ 0x8fdfe7bde0000000#64 ++ 0xfffffff0000000f7#64 ++ 0x8ffffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x19883ff87f1e3fbd 0xd319883ff87f1e3f

def z1 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0fc1ff87e3c77e 0xfc1e0fc1ff87e3c7

def z2 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6318440ffffdc 0xb0e7f6318440ffff

def z3 : W := mkw 0x9dc014a000000000 0x0f9dc014a0000000 0xfff83ff0000000f7 0x8ffff83ff0000000

def z4 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff0000ffffc00ff 0x7ffff0000ffffc00

def z5 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff0000000f7 0x8ffffffff0000000

def z6 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe00ffe0ff803f8fb 0xefe00ffe0ff803f8

def z7 : W := mkw 0x42a631800024dba0 0x9042a631800024db 0x01863180401fff9c 0x9001863180401fff

def z8 : W := mkw 0x090806381b122440 0x41090806381b1224 0x19880e787f1c00bd 0x5319880e787f1c00

def z9 : W := mkw 0x0008001801020400 0x0000080018010204 0x180801f80702073c 0xd0180801f8070207

def z10 : W := mkw 0xe00d6a1ee903b401 0x0ae00d6a1ee903b4 0xf80fffffff03ffff 0xfff80fffffff03ff

def z11 : W := mkw 0xdfe7bfe01a1429c4 0xcfdfe7bfe01a1429 0xfffffff0781c38f7 0x8ffffffff0781c38

def z12 : W := mkw 0x0000000012100000 0x0000000000121000 0x000000087f1c0008 0x50000000087f1c00

def z13 : W := mkw 0xc9e53ca000000004 0x8bc9e53ca0000000 0xe1fffe00000000f3 0x8fe1fffe00000000

def z14 : W := mkw 0xbd50000776fcdba2 0x1fbd50000776fcdb 0xfff0000fffffffff 0x7ffff0000fffffff

def z15 : W := mkw 0x1408c05985830400 0x241408c059858304 0x1809c1fb8702073e 0xdc1809c1fb870207

def z16 : W := mkw 0xa950000672580002 0x0ba9500006725800 0xe1f00000781c0081 0x03e1f00000781c00

def z17 : W := mkw 0xbf5ac15ff7fb4602 0x2fbf5ac15ff7fb46 0xffffc1ffffffc7ff 0xffffffc1ffffffc7

def z18 : W := mkw 0x9d48c05bb7930402 0x2f9d48c05bb79304 0x1809c07bbf000023 0x4f1809c07bbf0000

def z19 : W := mkw 0x960bcb5bada36601 0x2e960bcb5bada366 0x1e0fcfffbfe3c77f 0xff1e0fcfffbfe3c7

def z20 : W := mkw 0xfffe37bf7ffeffe2 0xdffffe37bf7ffeff 0xfffe3fffffffffff 0xfffffe3fffffffff

def z21 : W := mkw 0x008816b809062dc0 0x40008816b809062d 0x00083ff000023f00 0x8000083ff000023f

def z22 : W := mkw 0xb450000764c80002 0x0eb450000764c800 0xe670000780e00042 0x2ce670000780e000

def z23 : W := mkw 0x6bb637a45a7cfbe0 0xd16bb637a45a7cfb 0xe7f63f8478ffffdd 0xb3e7f63f8478ffff

def z24 : W := mkw 0x0008001801020400 0x0000080018010204 0x1808007807000020 0x4018080078070000

def z25 : W := mkw 0x0900043013100440 0x4109000430131004 0x1800007007000000 0x0018000070070000

def z26 : W := mkw 0x1400000104800000 0x0414000001048000 0x1e00000f87e0007e 0x7c1e00000f87e000

def z27 : W := mkw 0xcbe7bde000000004 0x8bcbe7bde0000000 0xe1fffff000000081 0x83e1fffff0000000

def z28 : W := mkw 0xdde53ca000000004 0x8fdde53ca0000000 0xfff03e00000000f7 0x0ffff03e00000000

def z29 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff000007ffc0085 0x13fff000007ffc00

def z30 : W := mkw 0x400d6a088803b001 0x00400d6a088803b0 0x000ffe000003f800 0x80000ffe000003f8

def z31 : W := mkw 0xa000000660000000 0x0aa0000006600000 0xe000000ff80000fb 0x6fe000000ff80000

def z32 : W := mkw 0xbdd816bf7fde2dc2 0x4fbdd816bf7fde2d 0xfff83ffffffe3fff 0xfffff83ffffffe3f

def z33 : W := mkw 0xfffffdfff7fb4606 0xaffffffdfff7fb46 0xffffffffffffc7ff 0xffffffffffffffc7

def z34 : W := mkw 0x098856b99fb76fc0 0x61098856b99fb76f 0x19883fffffffffbd 0xf319883fffffffff

def z35 : W := mkw 0x02a2118000000000 0x8002a21180000000 0x07f0018000000004 0x0007f00180000000

def z36 : W := mkw 0x9d418c6336900006 0x0f9d418c63369000 0x1809ce7bbf000023 0x4f1809ce7bbf0000

def z37 : W := mkw 0x42a7bde000000004 0x8042a7bde0000000 0x000ffff000000000 0x80000ffff0000000

def z38 : W := mkw 0xfff7bde776d80006 0x8ffff7bde776d800 0xfffffffffffc00ff 0xfffffffffffffc00

def z39 : W := mkw 0x168ad1d985a74f80 0x24168ad1d985a74f 0x1f8ff1ffc7fffffe 0xfc1f8ff1ffc7ffff

def z40 : W := mkw 0x9dc19ce000000004 0x0f9dc19ce0000000 0x1989fff0000000b7 0x8f1989fff0000000

def z41 : W := mkw 0xc00d680880030000 0x0ac00d6808800300 0xe00ffe0f8003c0fb 0xefe00ffe0f8003c0

def z42 : W := mkw 0xdfe7bde336900006 0x8fdfe7bde3369000 0xfffffffbbf0000f7 0xcffffffffbbf0000

def z43 : W := mkw 0xc005280000000000 0x0ac0052800000000 0xe00ffe00000000f3 0x8fe00ffe00000000

def z44 : W := mkw 0xffefffeee803b005 0x8fffefffeee803b0 0xfffffffff803f8ff 0xeffffffffff803f8

def z45 : W := mkw 0xe9e53ea66800b005 0x8be9e53ea66800b0 0xe1f03e0078003881 0x03e1f03e00780038

def z46 : W := mkw 0xe08d7a8ee807b981 0x0ae08d7a8ee807b9 0xe18fff8ff81fffff 0xffe18fff8ff81fff

def z47 : W := mkw 0x6084308440049980 0x0060843084400499 0xe1863184401fffdc 0xb0e1863184401fff

def z48 : W := mkw 0x9d40000000000000 0x0f9d400000000000 0xfff00000000000f7 0x0ffff00000000000

def z49 : W := mkw 0xfff7bde4406cdba4 0x9ffff7bde4406cdb 0xfffffff440ffffff 0xbffffffff440ffff

def z50 : W := mkw 0x361ac15ff7fb4602 0x24361ac15ff7fb46 0x1e0fc1ffffffc77e 0xfc1e0fc1ffffffc7

def z51 : W := mkw 0x62a631844024dba0 0x9062a631844024db 0xe00631844003ffd8 0xa0e00631844003ff

def z52 : W := mkw 0xf6f6318764ecdba2 0x9ef6f6318764ecdb 0xe7f63187c0ffffde 0xbce7f63187c0ffff

def z53 : W := mkw 0xdfeffdf985a34604 0xafdfeffdf985a346 0xffffffff87e3c7ff 0xffffffffff87e3c7

def z54 : W := mkw 0x020ac15881234600 0x20020ac158812346 0x000fc1f00003c700 0x80000fc1f00003c7

def z55 : W := mkw 0x42a631800024dba0 0x9042a631800024db 0x000631800003ff00 0x80000631800003ff

def z56 : W := mkw 0xdfe7bde00024dba4 0x9fdfe7bde00024db 0xfffffff00003fff7 0x8ffffffff00003ff

def z57 : W := mkw 0x9dc816b81b162dc0 0x4f9dc816b81b162d 0xfff83ff87f1e3fff 0xdffff83ff87f1e3f

def z58 : W := mkw 0x2910000452580000 0x0129100004525800 0xfff0000c7ffc00fd 0x73fff0000c7ffc00

def z59 : W := mkw 0x098014a000000000 0x01098014a0000000 0x19883ff0000000b5 0x8319883ff0000000

def z60 : W := mkw 0xdfefbff81b162dc4 0xcfdfefbff81b162d 0xfffffff87f1e3fff 0xdffffffff87f1e3f

def z61 : W := mkw 0x1f8ad7f99fb76fc0 0x651f8ad7f99fb76f 0x1f8fffffffffffff 0xff1f8fffffffffff

def z62 : W := mkw 0xf60feb5feda3f601 0x2ef60feb5feda3f6 0xfe0fffffffe3ffff 0xfffe0fffffffe3ff

def z63 : W := mkw 0x098014a0121409c0 0x41098014a0121409 0x01800000001c0000 0x0001800000001c00

def z64 : W := mkw 0x000802181b162dc0 0x40000802181b162d 0x000000087f1e3f08 0x50000000087f1e3f

def z65 : W := mkw 0xd667a94000000004 0x8ed667a940000000 0xe677c00000000042 0x0ce677c000000000

def z66 : W := mkw 0xe20f6b0ee823f201 0x0ae20f6b0ee823f2 0xe60fff8ff8e3ffff 0xffe60fff8ff8e3ff

def z67 : W := mkw 0xe0052a066800b001 0x0ae0052a066800b0 0xe00ffe00780038f3 0x8fe00ffe00780038

def z68 : W := mkw 0xfd552a077ed8b003 0x0ffd552a077ed8b0 0xfff03e0ffffc38ff 0x7ffff03e0ffffc38

def z69 : W := mkw 0x42b63180006c4ba0 0x9042b63180006c4b 0xe7f6318000fc07d4 0x90e7f6318000fc07

def z70 : W := mkw 0x20100004406cdba0 0x1020100004406cdb 0x0000000440ffff08 0x300000000440ffff

def z71 : W := mkw 0x9d418c6000000004 0x0f9d418c60000000 0x1809ce7000000023 0x0f1809ce70000000

def z72 : W := mkw 0x0000400184a14200 0x200000400184a142 0x0000000780e1c000 0x200000000780e1c0

def z73 : W := mkw 0x0008020808022000 0x0000080208080220 0x00083e08780238b9 0xc300083e08780238

def z74 : W := mkw 0x098014b013140dc0 0x41098014b013140d 0x198001f0071c0704 0x10198001f0071c07

def z75 : W := mkw 0x1602c14184a14200 0x241602c14184a142 0x1e07c00f87e1c07e 0x7c1e07c00f87e1c0

def z76 : W := mkw 0x2010000776d80002 0x002010000776d800 0x0000000ffffc0008 0x700000000ffffc00

def z77 : W := mkw 0x9d40000336900002 0x0f9d400003369000 0x1800000bbf000023 0x4f1800000bbf0000

def z78 : W := mkw 0x9f4bcd7985a34604 0x2f9f4bcd7985a346 0x1e0fcfff87e3c77f 0xff1e0fcfff87e3c7

def z79 : W := mkw 0x698c36bc5b16bdc0 0x41698c36bc5b16bd 0xf98e3ffc7f1ffffd 0xf3f98e3ffc7f1fff

def z80 : W := mkw 0x008816b81b162dc0 0x40008816b81b162d 0x00083ff87f1e3f08 0xd000083ff87f1e3f

def z81 : W := mkw 0x4005680080019001 0x0040056800800190 0x0007c0000001c000 0x000007c0000001c0

def z82 : W := mkw 0xe0052a066800b001 0x0ae0052a066800b0 0xe0003e0078003881 0x03e0003e00780038

def z83 : W := mkw 0xe0056806e0019001 0x0ae0056806e00190 0xe007c0078001c042 0x2ce007c0078001c0

def z84 : W := mkw 0x6004200440009000 0x0060042004400090 0xe00630044003f8d8 0xa0e00630044003f8

def z85 : W := mkw 0xe2bf7b8ee86ffba1 0x9ae2bf7b8ee86ffb 0xe7ffff8ff8ffffff 0xffe7ffff8ff8ffff

def z86 : W := mkw 0x008016a0080429c0 0x40008016a0080429 0x00003e0000003800 0x0000003e00000038

def z87 : W := mkw 0x42ae37b80926ffe0 0xd042ae37b80926ff 0x000e3ff00003ff00 0x80000e3ff00003ff

def z88 : W := mkw 0x090806381b122440 0x41090806381b1224 0x18080e783f000021 0x4318080e783f0000

def z89 : W := mkw 0x623621044068d220 0x90623621044068d2 0xe676000400e1c040 0x20e676000400e1c0

def z90 : W := mkw 0x020ac15881234600 0x20020ac158812346 0x000fc1ff8003c77a 0xec000fc1ff8003c7

def z91 : W := mkw 0x0000400080010000 0x0000004000800100 0x0007c0078001c042 0x2c0007c0078001c0

def z92 : W := mkw 0x098016a01a1429c0 0x41098016a01a1429 0x01803e00781c3881 0x0301803e00781c38

def z93 : W := mkw 0xe98d7ebefb17bdc1 0x4be98d7ebefb17bd 0xf98fffffff1fffff 0xfff98fffffff1fff

def z94 : W := mkw 0xc00d6a0aa8032001 0x0ac00d6a0aa80320 0xe00ffe0bb80000f3 0xcfe00ffe0bb80000

def z95 : W := mkw 0x0008401985a34600 0x200008401985a346 0x0000000f87e3c708 0x700000000f87e3c7

def z96 : W := mkw 0x60b43084406cdba0 0x9060b43084406cdb 0xe1f0300440ffff88 0x30e1f0300440ffff

def z97 : W := mkw 0x090802181b162dc0 0x41090802181b162d 0x198000087f1e3fbd 0x53198000087f1e3f

def z98 : W := mkw 0x20901084406cdba0 0x1020901084406cdb 0x0180318440ffff9c 0xb00180318440ffff

def z99 : W := mkw 0x0008401985830400 0x2000084019858304 0x0000000b87000000 0x400000000b870000

def z100 : W := mkw 0x1f8295f117b44fc0 0x651f8295f117b44f 0x1f8001f007fc0704 0x101f8001f007fc07

def z101 : W := mkw 0x1f0ac15997b34600 0x251f0ac15997b346 0x1f8fc1ffffffc7ff 0xff1f8fc1ffffffc7

def z102 : W := mkw 0xf60fe95fe5a3d601 0x2ef60fe95fe5a3d6 0xfe0fc1ff87e3c77e 0xfcfe0fc1ff87e3c7

def z103 : W := mkw 0xf40d6a0fec83b001 0x0ef40d6a0fec83b0 0xfe0ffe0fffe3f8ff 0xfffe0ffe0fffe3f8

def z104 : W := mkw 0xdfe7bde104800004 0x8fdfe7bde1048000 0xffffffff87e000ff 0xffffffffff87e000

def z105 : W := mkw 0x4bafbff81b162dc4 0xc14bafbff81b162d 0x198ffff87f1e3fbd 0xd3198ffff87f1e3f

def z106 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff0000787fc0046 0x3cfff0000787fc00

def z107 : W := mkw 0x0008400880030000 0x0000084008800300 0x000fc00f8003c07a 0xec000fc00f8003c0

def z108 : W := mkw 0x4bae37b81b162dc0 0xc14bae37b81b162d 0xfffe3ff87f1e3ffd 0xd3fffe3ff87f1e3f

def z109 : W := mkw 0xfd5d6a0ffedbb003 0x0ffd5d6a0ffedbb0 0xfffffe0ffffff8ff 0xfffffffe0ffffff8

def z110 : W := mkw 0xfdf53ca776d80006 0x8ffdf53ca776d800 0xfff03e0ffffc00ff 0x7ffff03e0ffffc00

def z111 : W := mkw 0x42afffe88803b005 0x8042afffe88803b0 0x000ffff00003f800 0x80000ffff00003f8

def z112 : W := mkw 0x0008400880030000 0x0000084008800300 0x000fc0000003c000 0x80000fc0000003c0

def z113 : W := mkw 0x1602814000000000 0x0416028140000000 0x1e0fc1f000000076 0x8c1e0fc1f0000000

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0x000fc00000000072 0x8c000fc000000000

def z115 : W := mkw 0x1fe295f105a04604 0xa51fe295f105a046 0x1ff001f007e00704 0x101ff001f007e007

def z116 : W := mkw 0xd607a94000000000 0x0ed607a940000000 0xfe0ffff0000000f7 0x8ffe0ffff0000000

def z117 : W := mkw 0x2008420ee803b001 0x002008420ee803b0 0x0000000ff803f808 0x600000000ff803f8

def z118 : W := mkw 0x7fbef7fddfffffe0 0xf57fbef7fddfffff 0xffffffffffffffff 0xffffffffffffffff

def z119 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfe70000fbfe00063 0x6ffe70000fbfe000

def z120 : W := mkw 0xa008020e68022000 0x0aa008020e680220 0xe0083e0ff80238fb 0xefe0083e0ff80238

def z121 : W := mkw 0x56a7bde000000004 0x8456a7bde0000000 0x1e0ffff000000076 0x8c1e0ffff0000000

def z122 : W := mkw 0x0bba17b81b7e6fe0 0xd10bba17b81b7e6f 0x1ff83ff87ffe3fbd 0xd31ff83ff87ffe3f

def z123 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0x0006318440ffff08 0xb00006318440ffff

def z124 : W := mkw 0x1d50000116d80002 0x051d50000116d800 0x1ff0000007fc0004 0x101ff0000007fc00

def z125 : W := mkw 0x0080108000040980 0x0000801080000409 0x01803180401e3f9c 0x9001803180401e3f

def z126 : W := mkw 0xdfe7bde000040984 0x8fdfe7bde0000409 0xfffffff0401e3fff 0x9ffffffff0401e3f

def z127 : W := mkw 0xdf67ad6000000004 0x8fdf67ad60000000 0xfe7fce7000000063 0x0ffe7fce70000000

def z128 : W := mkw 0xbd40000660000000 0x0fbd400006600000 0xfff0000ff80000ff 0x6ffff0000ff80000

def z129 : W := mkw 0x160ac14984a34200 0x24160ac14984a342 0x060fc00f80e3c07a 0xec060fc00f80e3c0

def z130 : W := mkw 0xb400000764800000 0x0eb4000007648000 0xfe00000fffe000ff 0x7ffe00000fffe000

def z131 : W := mkw 0x1f8a97f91fb66fc0 0x651f8a97f91fb66f 0x1f883ff87ffe3fbd 0xd31f883ff87ffe3f

def z132 : W := mkw 0x623621044068d220 0x90623621044068d2 0xe676018400e3c75c 0xb0e676018400e3c7

def z133 : W := mkw 0xe0056806e0019001 0x0ae0056806e00190 0xe00ffe078001c0f3 0xafe00ffe078001c0

def z134 : W := mkw 0xf60feb4ee803b001 0x0ef60feb4ee803b0 0xfe0ffffff803f8ff 0xeffe0ffffff803f8

def z135 : W := mkw 0x62be719dc5efdfa0 0xb062be719dc5efdf 0xe7f6318fc7ffffdc 0xf0e7f6318fc7ffff

def z136 : W := mkw 0x098016b01b142dc0 0x41098016b01b142d 0x19803ff07f1c3f85 0x1319803ff07f1c3f

def z137 : W := mkw 0x1602815105a04600 0x241602815105a046 0x1e0001f007e00704 0x101e0001f007e007

def z138 : W := mkw 0x160ac3599fb76fc0 0x64160ac3599fb76f 0x1e0fc1ffffffff7e 0xfc1e0fc1ffffffff

def z139 : W := mkw 0x2008421feda3f601 0x202008421feda3f6 0x0000000fffe3ff08 0x700000000fffe3ff

def z140 : W := mkw 0x42a6318000000000 0x8042a63180000000 0xe7f63180000000d4 0x80e7f63180000000

def z141 : W := mkw 0x9d50000336d80002 0x0f9d50000336d800 0x1ff0000bbffc0027 0x5f1ff0000bbffc00

def z142 : W := mkw 0xa010000660480000 0x0aa0100006604800 0xe7f0000ff8fc00ff 0x7fe7f0000ff8fc00

def z143 : W := mkw 0x0010000116d80002 0x000010000116d800 0x0000000007fc0000 0x100000000007fc00

def z144 : W := mkw 0x098014a012100000 0x01098014a0121000 0x19883ff87f1c00bd 0xd319883ff87f1c00

def z145 : W := mkw 0xfd55280776d80002 0x0ffd55280776d800 0xfffffe0ffffc00ff 0xfffffffe0ffffc00

def z146 : W := mkw 0x02b21180006c4ba0 0x9002b21180006c4b 0x07f0018000fc0704 0x1007f0018000fc07

def z147 : W := mkw 0x80094a0aa8032001 0x0a80094a0aa80320 0x0009ce0bb8000023 0x4f0009ce0bb80000

def z148 : W := mkw 0xa008420ee803b001 0x0aa008420ee803b0 0xe000000ff803f8fb 0x6fe000000ff803f8

def z149 : W := mkw 0x0008420888032000 0x0000084208880320 0x000ffe0ff803f8fb 0xef000ffe0ff803f8

def z150 : W := mkw 0x6bb635b4537cdfe0 0xd16bb635b4537cdf 0xfff631f447ffffdc 0xb0fff631f447ffff

def z151 : W := mkw 0xbd518c6776d80006 0x0fbd518c6776d800 0xfff9ce7ffffc00ff 0x7ffff9ce7ffffc00

def z152 : W := mkw 0xffe7bde440009004 0x8fffe7bde4400090 0xfffffff44003f8ff 0xaffffffff44003f8

def z153 : W := mkw 0x76b6318544ecdba0 0x9476b6318544ecdb 0xfff6318fc7fffffe 0xfcfff6318fc7ffff

def z154 : W := mkw 0xbd40000776900002 0x0fbd400007769000 0xf800000fff0000fb 0x6ff800000fff0000

def z155 : W := mkw 0x1fea97f81b162dc4 0xc51fea97f81b162d 0x1ff83ff87f1e3fbd 0xd31ff83ff87f1e3f

def z156 : W := mkw 0x1fe295e000000004 0x851fe295e0000000 0x1ff001f000000004 0x001ff001f0000000

def z157 : W := mkw 0x008014b001040dc0 0x40008014b001040d 0x000001f000000700 0x00000001f0000007

def z158 : W := mkw 0x1400000104800000 0x0414000001048000 0x1800000b87000022 0x4c1800000b870000

def z159 : W := mkw 0x42a7bde00024dba4 0x9042a7bde00024db 0x000ffff00003ff00 0x80000ffff00003ff

def z160 : W := mkw 0x8000000000000000 0x0a80000000000000 0xe0000000000000f3 0x0fe0000000000000

def z161 : W := mkw 0xdfefffe88803b005 0x8fdfefffe88803b0 0xfffffff00003f8f7 0x8ffffffff00003f8

def z162 : W := mkw 0x0900042000000000 0x0109000420000000 0x18080e7000000021 0x0318080e70000000

def z163 : W := mkw 0x1d40000116900002 0x051d400001169000 0x1800000007000000 0x0018000000070000

def z164 : W := mkw 0xbd50000440480000 0x0fbd500004404800 0xfff0000440fc00ff 0x3ffff0000440fc00

def z165 : W := mkw 0x008812981b162dc0 0x40008812981b162d 0x018031887f1e3f9c 0xd0018031887f1e3f

def z166 : W := mkw 0x9d40000336900002 0x0f9d400003369000 0x1980000bff1c00bf 0x5f1980000bff1c00

def z167 : W := mkw 0x40a4308000000000 0x8040a43080000000 0xe1f0300000000080 0x00e1f03000000000

def z168 : W := mkw 0xffff7b8ffefffba3 0x9fffff7b8ffefffb 0xffffff8fffffffff 0xffffffff8fffffff

def z169 : W := mkw 0x422621000020d220 0x90422621000020d2 0x000600000001c000 0x00000600000001c0

def z170 : W := mkw 0xfff7bde4404c99a4 0x9ffff7bde4404c99 0xfffffff0401c38f7 0x8ffffffff0401c38

def z171 : W := mkw 0xc9e53ca000000004 0x8bc9e53ca0000000 0xe1f03e0000000081 0x03e1f03e00000000

def z172 : W := mkw 0x2010000440480000 0x0020100004404800 0xe7f0000440fc00dc 0x30e7f0000440fc00

def z173 : W := mkw 0xf677a94764c80006 0x8ef677a94764c800 0xe677c00780e00042 0x2ce677c00780e000

def z174 : W := mkw 0xc9ed3eb81b162dc4 0xcbc9ed3eb81b162d 0xf9f83ff87f1e3fbd 0xd3f9f83ff87f1e3f

def z175 : W := mkw 0x0008021809062dc0 0x400008021809062d 0x0000000000023f00 0x000000000000023f

def z176 : W := mkw 0xe0bd7a8ee84fb9a1 0x9ae0bd7a8ee84fb9 0xe1fffe0ff81ff8fb 0xefe1fffe0ff81ff8

def z177 : W := mkw 0x6bbe37bc5b7effe0 0xd16bbe37bc5b7eff 0xfffe3ffc7ffffffd 0xf3fffe3ffc7fffff

def z178 : W := mkw 0x60b43084404c99a0 0x9060b43084404c99 0xe1f03000401c3880 0x00e1f03000401c38

def z179 : W := mkw 0x76bef1ddc5efdfa0 0xb476bef1ddc5efdf 0xfffff1ffc7fffffe 0xfcfffff1ffc7ffff

def z180 : W := mkw 0x02a295e000000004 0x8002a295e0000000 0x000001f000000000 0x00000001f0000000

def z181 : W := mkw 0xf60feb4feca3f201 0x2ef60feb4feca3f2 0xe60ffe0ff8e3f8fb 0xefe60ffe0ff8e3f8

def z182 : W := mkw 0x763ee15dc5ebd620 0xb4763ee15dc5ebd6 0xfe7fc1ff87e3c77e 0xfcfe7fc1ff87e3c7

def z183 : W := mkw 0xa900000672100000 0x0ba9000006721000 0xf980000fff1c00ff 0x7ff980000fff1c00

def z184 : W := mkw 0x1fe295e000000004 0x851fe295e0000000 0x1fffc1f000000076 0x8c1fffc1f0000000

def z185 : W := mkw 0x1602c15185a14600 0x241602c15185a146 0x1e07c1f787e1c746 0x3c1e07c1f787e1c7

def z186 : W := mkw 0x299816bc5b5e2dc0 0x41299816bc5b5e2d 0xfff83ffc7ffe3ffd 0xf3fff83ffc7ffe3f

def z187 : W := mkw 0x1f5ac15997fb4602 0x251f5ac15997fb46 0x1fffc1ff87ffc77e 0xfc1fffc1ff87ffc7

def z188 : W := mkw 0x0202c14080214200 0x200202c140802142 0x0007c0000001c000 0x000007c0000001c0

def z189 : W := mkw 0xe23f6b0ee86bf221 0x9ae23f6b0ee86bf2 0xe67ffe0ff8e3f8fb 0xefe67ffe0ff8e3f8

def z190 : W := mkw 0x9440000000000000 0x0e94400000000000 0xe670000000000042 0x0ce6700000000000

def z191 : W := mkw 0x1602010104a04200 0x041602010104a042 0x1e06018f87e3c77e 0xfc1e06018f87e3c7

def z192 : W := mkw 0x62be738ee86ffba1 0x9062be738ee86ffb 0xe7f6318ff8ffffdc 0xf0e7f6318ff8ffff

def z193 : W := mkw 0xb450000776d80002 0x0eb450000776d800 0xe670000ffffc004a 0x7ce670000ffffc00

def z194 : W := mkw 0xf6f7b9c4406cdba4 0x9ef6f7b9c4406cdb 0xe7f7f18440ffffde 0xbce7f7f18440ffff

def z195 : W := mkw 0xdfefbfe808022004 0x8fdfefbfe8080220 0xfffffff8780238ff 0xcffffffff8780238

def z196 : W := mkw 0x1ff295e116d80006 0x851ff295e116d800 0x1ff001f007fc0004 0x101ff001f007fc00

def z197 : W := mkw 0x1602c14184a14200 0x241602c14184a142 0x0607c00780e1c042 0x2c0607c00780e1c0

def z198 : W := mkw 0x20004006e0019001 0x0020004006e00190 0x000000078001c000 0x20000000078001c0

def z199 : W := mkw 0x600c620ee803b001 0x00600c620ee803b0 0xe006300ff803f8d8 0xe0e006300ff803f8

def z200 : W := mkw 0x6004200440009000 0x0060042004400090 0xe00600040001c040 0x20e00600040001c0

def z201 : W := mkw 0x42a631800024dba0 0x9042a631800024db 0x0606318400e3ff5c 0xb00606318400e3ff

def z202 : W := mkw 0xa000000660000000 0x0aa0000006600000 0xe000000078000081 0x03e0000000780000

def z203 : W := mkw 0x2008420ee803b001 0x002008420ee803b0 0x000fc00ff803f87a 0xec000fc00ff803f8

def z204 : W := mkw 0xe0b53a86684cb9a1 0x9ae0b53a86684cb9 0xe1f03e00781c3881 0x03e1f03e00781c38

def z205 : W := mkw 0xc00d2a0808022000 0x0ac00d2a08080220 0xe00ffe08780238fb 0xcfe00ffe08780238

def z206 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfff7c1f000000046 0x0cfff7c1f0000000

def z207 : W := mkw 0x0202010000204200 0x0002020100002042 0x0606018400e3c75c 0xb00606018400e3c7

def z208 : W := mkw 0xdde5bce000000004 0x8fdde5bce0000000 0xf9f9fe70000000a3 0x0ff9f9fe70000000

def z209 : W := mkw 0x1f8295e000000000 0x051f8295e0000000 0x1f8ffff0000000f7 0x8f1f8ffff0000000

def z210 : W := mkw 0x408d7eb88907bdc1 0x40408d7eb88907bd 0x000ffff00003ff00 0x80000ffff00003ff

def z211 : W := mkw 0xfff6318776fcdba2 0x9ffff6318776fcdb 0xfff6318fffffffff 0xfffff6318fffffff

def z212 : W := mkw 0xbff2118776fc4ba2 0x9fbff2118776fc4b 0xfff0018ffffc07ff 0x7ffff0018ffffc07

def z213 : W := mkw 0x0980108012140980 0x0109801080121409 0x198031887f1e3fbd 0xd3198031887f1e3f

def z214 : W := mkw 0xa0094a0ee803b001 0x0aa0094a0ee803b0 0x0009ce0ff803f82b 0x6f0009ce0ff803f8

def z215 : W := mkw 0x2018420ffedbb003 0x002018420ffedbb0 0x0000000ffffff808 0x700000000ffffff8

def z216 : W := mkw 0x160ac15881234600 0x24160ac158812346 0x1e0fc1f00003c776 0x8c1e0fc1f00003c7

def z217 : W := mkw 0x3410000776d80002 0x043410000776d800 0x1e00000ffffc007e 0x7c1e00000ffffc00

def z218 : W := mkw 0x2018420ee86ffba1 0x102018420ee86ffb 0x0000000ff8ffff08 0x700000000ff8ffff

def z219 : W := mkw 0xe90d6e3efb13b441 0x4be90d6e3efb13b4 0xf80ffe7fff03f8fb 0xeff80ffe7fff03f8

def z220 : W := mkw 0x89094e3abb132441 0x4b89094e3abb1324 0x1809ce7bbf000023 0x4f1809ce7bbf0000

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0xe7f00000000000d4 0x00e7f00000000000

def z222 : W := mkw 0x0010000000480000 0x0000100000004800 0x07f0000000fc0004 0x1007f0000000fc00

def z223 : W := mkw 0x42af7b888827fba1 0x9042af7b888827fb 0x000fff800003ff00 0x80000fff800003ff

def z224 : W := mkw 0x160ac14880030000 0x04160ac148800300 0x1e0fc1ff8003c07e 0xec1e0fc1ff8003c0

def z225 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe0003e0ff803f889 0x63e0003e0ff803f8

def z226 : W := mkw 0x02b21180006c4ba0 0x9002b21180006c4b 0x07f6018400ffc75c 0xb007f6018400ffc7

def z227 : W := mkw 0x8001080000000000 0x0a80010800000000 0x0009ce0000000023 0x0f0009ce00000000

def z228 : W := mkw 0x62be37bc496effe0 0xd062be37bc496eff 0xe7fe3ff440ffffdc 0xb0e7fe3ff440ffff

def z229 : W := mkw 0x0908001813120400 0x0109080018131204 0x198801f87f1e07bd 0xd3198801f87f1e07

def z230 : W := mkw 0xe01d6a0ee84bb001 0x0ae01d6a0ee84bb0 0xe7fffe0ff8fff8ff 0xffe7fffe0ff8fff8

def z231 : W := mkw 0xbf52815777f84602 0x2fbf52815777f846 0xfff001fffffc07ff 0x7ffff001fffffc07

def z232 : W := mkw 0xe004200660009000 0x0ae0042006600090 0xe006300ff803f8fb 0xefe006300ff803f8

def z233 : W := mkw 0xe2b73984406cdba0 0x9ae2b73984406cdb 0xe7ffff8440ffffff 0xbfe7ffff8440ffff

def z234 : W := mkw 0x0900000000000000 0x0109000000000000 0x19800000000000b5 0x0319800000000000

def z235 : W := mkw 0xfffef1dff7ffdfa2 0xbffffef1dff7ffdf 0xfffff1ffffffffff 0xfffffff1ffffffff

def z236 : W := mkw 0x9f438d6000000004 0x0f9f438d60000000 0x1e0fcff000000077 0x8f1e0fcff0000000

def z237 : W := mkw 0xb65ac15fe5eb4602 0x2eb65ac15fe5eb46 0xfe7fc1ff87e3c77e 0xfcfe7fc1ff87e3c7

def z238 : W := mkw 0x600d6a0cc803b001 0x00600d6a0cc803b0 0xe00ffe044003f8d8 0xa0e00ffe044003f8

def z239 : W := mkw 0x028ad7f889276fc0 0x60028ad7f889276f 0x000ffff00003ff00 0x80000ffff00003ff

def z240 : W := mkw 0xe95d6a0efa5bb003 0x0be95d6a0efa5bb0 0xe1fffe0ff81ff8fb 0xefe1fffe0ff81ff8

def z241 : W := mkw 0x42a7bde000000004 0x8042a7bde0000000 0xe7fffff0000000d4 0x80e7fffff0000000

def z242 : W := mkw 0xbd58001f77da0402 0x0fbd58001f77da04 0xfff801fffffe07ff 0xfffff801fffffe07

def z243 : W := mkw 0x201000044068d220 0x10201000044068d2 0x0000000400e1c000 0x200000000400e1c0

def z244 : W := mkw 0x0008021809022400 0x0000080218090224 0x18083ff87f023fbd 0xd318083ff87f023f

def z245 : W := mkw 0x7636e145c4e9d220 0xb47636e145c4e9d2 0xe677c00780e1c042 0x2ce677c00780e1c0

def z246 : W := mkw 0x2010000776fcdba2 0x102010000776fcdb 0x0000000fffffff08 0x700000000fffffff

def z247 : W := mkw 0x1602814104a04200 0x241602814104a042 0x0600000000e00000 0x000600000000e000

def z248 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe00fce0fb801c063 0x6fe00fce0fb801c0

def z249 : W := mkw 0xdfeffde880030004 0x8fdfeffde8800300 0xffffffff8003c0ff 0xefffffffff8003c0

def z250 : W := mkw 0x1d08c6799f932440 0x651d08c6799f9324 0x1809ce7bbf000023 0x4f1809ce7bbf0000

def z251 : W := mkw 0x0bb215b0137c4fe0 0xd10bb215b0137c4f 0x1ff001f007fc0704 0x101ff001f007fc07

def z252 : W := mkw 0xffffbfff7fde2dc6 0xcfffffbfff7fde2d 0xfffffffffffe3fff 0xfffffffffffffe3f

def z253 : W := mkw 0xe2af7b8ee803b001 0x8ae2af7b8ee803b0 0xe7ffff8ff803f8ff 0xefe7ffff8ff803f8

def z254 : W := mkw 0x9f4ac15985a34600 0x2f9f4ac15985a346 0xffffc1ff87e3c7ff 0xffffffc1ff87e3c7

def z255 : W := mkw 0x360ac35feda3f601 0x24360ac35feda3f6 0x1e0fc1ffffe3ff7e 0xfc1e0fc1ffffe3ff

def z256 : W := mkw 0xbf52010776f84202 0x0fbf52010776f842 0xfff6018fffffc7ff 0xfffff6018fffffc7

def z257 : W := mkw 0x80010a0228002001 0x0a80010a02280020 0x00000e0038000001 0x0300000e00380000

def z258 : W := mkw 0x6004200440009000 0x0060042004400090 0xe000300040003880 0x00e0003000400038

def z259 : W := mkw 0xe9552a067a58b003 0x0be9552a067a58b0 0xe1f03e00781c3881 0x03e1f03e00781c38

def z260 : W := mkw 0xa000000660000000 0x0aa0000006600000 0xe000000780000042 0x2ce0000007800000

def z261 : W := mkw 0x0000000000204200 0x0000000000002042 0x0000000400e3c708 0x300000000400e3c7

def z262 : W := mkw 0x400d6a088803b001 0x00400d6a088803b0 0x000ffe0f8003f87a 0xec000ffe0f8003f8

def z263 : W := mkw 0xfff7bde764c80006 0x8ffff7bde764c800 0xfffffff780e000f7 0xaffffffff780e000

def z264 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z265 : W := mkw 0x62bef1dcc16fdfa0 0xb062bef1dcc16fdf 0xe7fff1f440ffffdc 0xb0e7fff1f440ffff

def z266 : W := mkw 0x0000000336900002 0x0000000003369000 0x0000000bbf000000 0x400000000bbf0000

def z267 : W := mkw 0xdfe7fde184a14204 0xafdfe7fde184a142 0xfffffff780e1c0f7 0xaffffffff780e1c0

def z268 : W := mkw 0x1408c05985830400 0x241408c059858304 0x1809c07b87000022 0x4c1809c07b870000

def z269 : W := mkw 0x20100004404c99a0 0x1020100004404c99 0x00000000401c3800 0x0000000000401c38

def z270 : W := mkw 0x1dd014b117dc0dc2 0x451dd014b117dc0d 0x1ff001f007fc0704 0x101ff001f007fc07

def z271 : W := mkw 0xdf67a94000000004 0x8fdf67a940000000 0xfff7c000000000f7 0x0ffff7c000000000

def z272 : W := mkw 0x69bc36bc5b5ebde0 0xd169bc36bc5b5ebd 0xf9f83ff87f1e3fbd 0xd3f9f83ff87f1e3f

def z273 : W := mkw 0x098816b809062dc0 0x41098816b809062d 0x19883ff000023fb5 0x8319883ff000023f

def z274 : W := mkw 0x0080108000040980 0x0000801080000409 0x0000318000023f00 0x800000318000023f

def z275 : W := mkw 0x8000000220000000 0x0a80000002200000 0x0000000bb8000023 0x4f0000000bb80000

def z276 : W := mkw 0x62b7bde4406cdba4 0x9062b7bde4406cdb 0xe7fffff440ffffdc 0xb0e7fffff440ffff

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x000001800002071c 0x9000000180000207

def z278 : W := mkw 0xe0056a06e801b001 0x0ae0056a06e801b0 0xe007fe07f801f8c3 0x2fe007fe07f801f8

def z279 : W := mkw 0x0080108000000000 0x0000801080000000 0x0180318000000094 0x8001803180000000

def z280 : W := mkw 0xb450000764c80002 0x0eb450000764c800 0xe7f00007c0fc00de 0x3ce7f00007c0fc00

def z281 : W := mkw 0x5fe7bde000000004 0x855fe7bde0000000 0x1ffffff000000004 0x801ffffff0000000

def z282 : W := mkw 0x0008001801020400 0x0000080018010204 0x0000000807020708 0x5000000008070207

def z283 : W := mkw 0x60b43084404c99a0 0x9060b43084404c99 0xe1f63004401ff8d8 0xa0e1f63004401ff8

def z284 : W := mkw 0x4004200000000000 0x0040042000000000 0xe0063000000000d0 0x80e0063000000000

def z285 : W := mkw 0xb450000764c80002 0x0eb450000764c800 0xe670000ff8e000fb 0x6fe670000ff8e000

def z286 : W := mkw 0xfdf4308776dc99a2 0x9ffdf4308776dc99 0xfff0300ffffc38ff 0x7ffff0300ffffc38

def z287 : W := mkw 0x22b21184406c4ba0 0x9022b21184406c4b 0xe7f0018440fc07dc 0x30e7f0018440fc07

def z288 : W := mkw 0x56affdf985a34604 0xa456affdf985a346 0x1e0fffff87e3c77e 0xfc1e0fffff87e3c7

def z289 : W := mkw 0xd667a94000000004 0x8ed667a940000000 0xfe7fc1f000000076 0x8cfe7fc1f0000000

def z290 : W := mkw 0xbdd0108776dc0982 0x0fbdd0108776dc09 0xfff0318ffffe3fff 0xfffff0318ffffe3f

def z291 : W := mkw 0x4bae37b81b36ffe0 0xd14bae37b81b36ff 0x198e3ff87f1fffbd 0xd3198e3ff87f1fff

def z292 : W := mkw 0xc2a7398000000000 0x8ac2a73980000000 0xe7ffff80000000f7 0x8fe7ffff80000000

def z293 : W := mkw 0x600d6a0ee803b001 0x00600d6a0ee803b0 0x000ffe0ff803f808 0xe0000ffe0ff803f8

def z294 : W := mkw 0xc98d3eb81b162dc0 0x4bc98d3eb81b162d 0xf98ffff87f1e3fff 0xdff98ffff87f1e3f

def z295 : W := mkw 0x0008063809022440 0x4000080638090224 0x00080e7000000000 0x0000080e70000000

def z296 : W := mkw 0x160a815801020400 0x04160a8158010204 0x1e0fc1f80702077e 0xdc1e0fc1f8070207

def z297 : W := mkw 0xfffffdfdc5efdfa4 0xbffffffdfdc5efdf 0xffffffffc7ffffff 0xffffffffffc7ffff

def z298 : W := mkw 0x89410c2000000004 0x0b89410c20000000 0x00000e0000000001 0x0300000e00000000

def z299 : W := mkw 0x600c600cc0039000 0x00600c600cc00390 0xe00ff00fc003f8fa 0xece00ff00fc003f8

def z300 : W := mkw 0xe9f53ca672580006 0x8be9f53ca6725800 0xe1f03e00781c0081 0x03e1f03e00781c00

def z301 : W := mkw 0xc00d6a088803b001 0x0ac00d6a088803b0 0xe00ffe000003f8f3 0x8fe00ffe000003f8

def z302 : W := mkw 0xc9e53ca000000004 0x8bc9e53ca0000000 0xf9f83ff0000000b5 0x83f9f83ff0000000

def z303 : W := mkw 0x0232010000684220 0x9002320100006842 0x0670000000e00000 0x000670000000e000

def z304 : W := mkw 0x00b01080004c09a0 0x9000b01080004c09 0x01f00000001c0000 0x0001f00000001c00

def z305 : W := mkw 0x1602c14184a14200 0x241602c14184a142 0x1e0fc1f780e1c076 0xac1e0fc1f780e1c0

def z306 : W := mkw 0x9dc816bb3f962dc2 0x4f9dc816bb3f962d 0x19883ffbff1e3fbf 0xdf19883ffbff1e3f

def z307 : W := mkw 0x0b8a17b81b366fc0 0x410b8a17b81b366f 0x1f8e3ffc7ffffffd 0xf31f8e3ffc7fffff

def z308 : W := mkw 0xcbe73da000000004 0x8bcbe73da0000000 0xe7f63f80000000d5 0x83e7f63f80000000

def z309 : W := mkw 0x2010000672580002 0x0020100006725800 0x00000000781c0000 0x0000000000781c00

def z310 : W := mkw 0xe2afffeee803b005 0x8ae2afffeee803b0 0xe00ffffff803f8fb 0xefe00ffffff803f8

def z311 : W := mkw 0x80094a0aa8032001 0x0a80094a0aa80320 0x0009fe0bf80238bb 0xcf0009fe0bf80238

def z312 : W := mkw 0xc9e53ea01a1429c4 0xcbc9e53ea01a1429 0xe1f03e00781c3881 0x03e1f03e00781c38

def z313 : W := mkw 0xe0052a066800b001 0x0ae0052a066800b0 0xe0063e047803f8d9 0xa3e0063e047803f8

def z314 : W := mkw 0xdff7bde116d80006 0x8fdff7bde116d800 0xfffffff007fc00f7 0x9ffffffff007fc00

def z315 : W := mkw 0x9d498e781b122444 0x4f9d498e781b1224 0x1809ce783f000023 0x4f1809ce783f0000

def z316 : W := mkw 0x9d418c6000000004 0x0f9d418c60000000 0xfff9ce70000000f7 0x0ffff9ce70000000

def z317 : W := mkw 0xbdd014b777dc0dc2 0x4fbdd014b777dc0d 0xfff001fffffc07ff 0x7ffff001fffffc07

def z318 : W := mkw 0xe2b73b86686cfba1 0x9ae2b73b86686cfb 0xe7f63f8478ffffdd 0xb3e7f63f8478ffff

def z319 : W := mkw 0x0b8ad7f89b376fc0 0x610b8ad7f89b376f 0x198ffff87f1fffbd 0xd3198ffff87f1fff

def z320 : W := mkw 0xfff6318776d80002 0x8ffff6318776d800 0xfff6318ffffc00ff 0xfffff6318ffffc00

def z321 : W := mkw 0x62a6318440009000 0x8062a63184400090 0xe7f631844003f8dc 0xa0e7f631844003f8

def z322 : W := mkw 0xbf52814776d80002 0x0fbf52814776d800 0xffffc1fffffc00ff 0xffffffc1fffffc00

def z323 : W := mkw 0xbfdad7ffffff6fc2 0x6fbfdad7ffffff6f 0xffffffffffffffff 0xffffffffffffffff

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000300040023898 0x8000003000400238

def z325 : W := mkw 0x3410000544c80000 0x043410000544c800 0xfff0000fc7fc00fe 0x7cfff0000fc7fc00

def z326 : W := mkw 0xa98816be7b162dc0 0x4ba98816be7b162d 0xf9883fffff1e3fff 0xfff9883fffff1e3f

def z327 : W := mkw 0x1d50000116d80002 0x051d50000116d800 0x1ff0000f87fc007e 0x7c1ff0000f87fc00

def z328 : W := mkw 0x62b6318440480000 0x8062b63184404800 0xe7f6318440fc00dc 0xb0e7f6318440fc00

def z329 : W := mkw 0x69b436a45a5cb9e0 0xd169b436a45a5cb9 0xe1f03e00781c3881 0x03e1f03e00781c38

def z330 : W := mkw 0x4ba635a000000000 0x814ba635a0000000 0xfffe3ff0000000f5 0x83fffe3ff0000000

def z331 : W := mkw 0x1602814000000000 0x0416028140000000 0x1e0001f000000004 0x001e0001f0000000

def z332 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe1f63180401fff80 0x80e1f63180401fff

def z333 : W := mkw 0x60b43084404c99a0 0x9060b43084404c99 0xe7f0300440fc38dc 0x30e7f0300440fc38

def z334 : W := mkw 0x4004200000009000 0x0040042000000090 0x000630000003f800 0x80000630000003f8

def z335 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6300440fdf8c0 0x20e7f6300440fdf8

def z336 : W := mkw 0x22b21184406cdba0 0x9022b21184406cdb 0x07f0018440ffff0c 0x3007f0018440ffff

def z337 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0fc07f87e1c062 0x6c1e0fc07f87e1c0

def z338 : W := mkw 0xa950000672580002 0x0ba9500006725800 0xe1f0000ff81c00fb 0x6fe1f0000ff81c00

def z339 : W := mkw 0x0282118000244b80 0x000282118000244b 0x0786318440ffffdc 0xb00786318440ffff

def z340 : W := mkw 0xa010000776d80002 0x0aa010000776d800 0xe000000ffffc00fb 0x7fe000000ffffc00

def z341 : W := mkw 0x0900000012100000 0x0109000000121000 0x198000087f1c00bd 0x53198000087f1c00

def z342 : W := mkw 0x1408c05985830400 0x241408c059858304 0x180fc07f8703c07a 0xec180fc07f8703c0

def z343 : W := mkw 0x62b6318776fcdba2 0x9062b6318776fcdb 0xe7f6318fffffffdc 0xf0e7f6318fffffff

def z344 : W := mkw 0x090802081a122000 0x01090802081a1220 0x19883e087f1e38bd 0xd319883e087f1e38

def z345 : W := mkw 0xdfe7bde012100004 0x8fdfe7bde0121000 0xfffffff87f1c00ff 0xdffffffff87f1c00

def z346 : W := mkw 0x2010000776d80002 0x002010000776d800 0xe7f0000ffffc00dc 0x70e7f0000ffffc00

def z347 : W := mkw 0x000842088803b001 0x00000842088803b0 0x000000000003f800 0x00000000000003f8

def z348 : W := mkw 0x1602815105a04600 0x241602815105a046 0x1e0001ff87e0077e 0x7c1e0001ff87e007

def z349 : W := mkw 0x1fead5f985a34604 0xa51fead5f985a346 0x1fffc1ff87e3c77e 0xfc1fffc1ff87e3c7

def z350 : W := mkw 0xbd58020f7eda2002 0x0fbd58020f7eda20 0xfff83e0ffffe38ff 0xfffff83e0ffffe38

def z351 : W := mkw 0xc005280000000000 0x0ac0052800000000 0xe0003e0000000081 0x03e0003e00000000

def z352 : W := mkw 0x42a6318000204200 0x8042a63180002042 0xe7f6318400e3c7dc 0xb0e7f6318400e3c7

def z353 : W := mkw 0xe2376906e069d221 0x9ae2376906e069d2 0xe677c00780e1c042 0x2ce677c00780e1c0

def z354 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xe7f7fe00000000c3 0x0fe7f7fe00000000

def z355 : W := mkw 0x0000001001000400 0x0000000010010004 0x180001f007000704 0x10180001f0070007

def z356 : W := mkw 0x0008020808022000 0x0000080208080220 0x0000000878023808 0x4000000008780238

def z357 : W := mkw 0x160ac3598da36600 0x24160ac3598da366 0x1e0fffffffe3ffff 0xff1e0fffffffe3ff

def z358 : W := mkw 0xa950000672580002 0x0ba9500006725800 0xf9f000087f1c00bd 0x53f9f000087f1c00

def z359 : W := mkw 0x0900000012100000 0x0109000000121000 0x180000083f000021 0x43180000083f0000

def z360 : W := mkw 0xc00d6a0aa803b001 0x0ac00d6a0aa803b0 0x000ffe0bb803f823 0xcf000ffe0bb803f8

def z361 : W := mkw 0xdd45280000000000 0x0fdd452800000000 0xfffffe00000000f7 0x8ffffffe00000000

def z362 : W := mkw 0xdfeffdf881234604 0xafdfeffdf8812346 0xfffffff00003c7f7 0x8ffffffff00003c7

def z363 : W := mkw 0xbd594a0ffedb2003 0x0fbd594a0ffedb20 0xfff9ce0ffffc00ff 0x7ffff9ce0ffffc00

def z364 : W := mkw 0x5fe6b5e000000004 0x855fe6b5e0000000 0xfff631f0000000d4 0x80fff631f0000000

def z365 : W := mkw 0x3d50000776d80002 0x053d50000776d800 0x1ff0000ffffc000c 0x701ff0000ffffc00

def z366 : W := mkw 0x1f8ad5f985a34600 0x251f8ad5f985a346 0x1f8fffff87e3c7ff 0xff1f8fffff87e3c7

def z367 : W := mkw 0x7ff6318556fcdba2 0x957ff6318556fcdb 0xfff6318447ffffdc 0xb0fff6318447ffff

def z368 : W := mkw 0xb450000764c80002 0x0eb450000764c800 0xfe70000f87e0007e 0x7cfe70000f87e000

def z369 : W := mkw 0x0950000012580002 0x0109500000125800 0x01f00000001c0000 0x0001f00000001c00

def z370 : W := mkw 0xbd58063f7fda2442 0x4fbd58063f7fda24 0xfff80e7ffffc00ff 0x7ffff80e7ffffc00

def z371 : W := mkw 0xd6e7bde000000004 0x8ed6e7bde0000000 0xe67ffff000000042 0x8ce67ffff0000000

def z372 : W := mkw 0x1400c04184810000 0x241400c041848100 0x0001c00380000002 0x0c0001c003800000

def z373 : W := mkw 0x0202010000204200 0x0002020100002042 0x0600018000e00704 0x100600018000e007

def z374 : W := mkw 0x098814b801020400 0x01098814b8010204 0x19883ff8070207bd 0xd319883ff8070207

def z375 : W := mkw 0x42aef1d88127dfa0 0xb042aef1d88127df 0x000ff1f00003ff00 0x80000ff1f00003ff

def z376 : W := mkw 0x1ff295e0006c4ba4 0x951ff295e0006c4b 0x1ff001f000fc0704 0x101ff001f000fc07

def z377 : W := mkw 0x42a6318000040980 0x8042a63180000409 0xe7f63180401e3fdc 0x90e7f63180401e3f

def z378 : W := mkw 0xdfefffeaa8032005 0x8fdfefffeaa80320 0xfffffffbb80000f7 0xcffffffffbb80000

def z379 : W := mkw 0x4005280000000000 0x0040052800000000 0x000ffe0000000000 0x80000ffe00000000

def z380 : W := mkw 0x1602815105a04600 0x241602815105a046 0x1e0fc1f007e00776 0x9c1e0fc1f007e007

def z381 : W := mkw 0xf66feb4ee803b005 0x8ef66feb4ee803b0 0xe67ffe0ff803f8fb 0xefe67ffe0ff803f8

def z382 : W := mkw 0xdff7bde0006c4ba4 0x9fdff7bde0006c4b 0xfffffff000fc07f7 0x9ffffffff000fc07

def z383 : W := mkw 0x9d40000104800000 0x0f9d400001048000 0xfff0000f87e000ff 0x7ffff0000f87e000

def z384 : W := mkw 0x42affdf881234604 0xa042affdf8812346 0x000ffff00003c700 0x80000ffff00003c7

def z385 : W := mkw 0xe00d6a1feda3f601 0x2ae00d6a1feda3f6 0xe00ffe0fffe3fffb 0xffe00ffe0fffe3ff

def z386 : W := mkw 0xfd4d6a0ee803b001 0x0ffd4d6a0ee803b0 0xfffffe0ff803f8ff 0xeffffffe0ff803f8

def z387 : W := mkw 0x168ad7f98da76fc0 0x64168ad7f98da76f 0x1e0fffff87e3ff7e 0xfc1e0fffff87e3ff

def z388 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0x180ffff000000023 0x8f180ffff0000000

def z389 : W := mkw 0x1602814104800000 0x0416028141048000 0x1e0fc1ff87e0007e 0xfc1e0fc1ff87e000

def z390 : W := mkw 0x008014a000000000 0x00008014a0000000 0x00083ff000000000 0x8000083ff0000000

def z391 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe00ffe007803f881 0x83e00ffe007803f8

def z392 : W := mkw 0x2010000764c80002 0x002010000764c800 0x0000000780e00000 0x200000000780e000

def z393 : W := mkw 0xebf63186727cdba2 0x9bebf63186727cdb 0xe7f6318478ffffdd 0xb3e7f6318478ffff

def z394 : W := mkw 0x498d7eb89b17bdc1 0x41498d7eb89b17bd 0x198ffff87f1fffbd 0xd3198ffff87f1fff

def z395 : W := mkw 0xff77a94776d80006 0x8fff77a94776d800 0xfff7c00ffffc00ff 0x7ffff7c00ffffc00

def z396 : W := mkw 0xffe7bfe66800b005 0x8fffe7bfe66800b0 0xfffffff0780038f7 0x8ffffffff0780038

def z397 : W := mkw 0x00018c6000000004 0x0000018c60000000 0x0009ce7000000000 0x000009ce70000000

def z398 : W := mkw 0x6bb63184527cdba0 0x916bb63184527cdb 0xfff6318c7ffffffd 0xf3fff6318c7fffff

def z399 : W := mkw 0x420feb588923f601 0x20420feb588923f6 0x000ffff00003ff00 0x80000ffff00003ff

def z400 : W := mkw 0xdfeffff99fb76fc4 0xefdfeffff99fb76f 0xffffffffffffffff 0xffffffffffffffff

def z401 : W := mkw 0x0900000012100000 0x0109000000121000 0x01800000781c0081 0x0301800000781c00

def z402 : W := mkw 0x1602c14184a14200 0x241602c14184a142 0x0607c18780e3c75e 0xbc0607c18780e3c7

def z403 : W := mkw 0xdfefbff809062dc4 0xcfdfefbff809062d 0xfffffff000023ff7 0x8ffffffff000023f

def z404 : W := mkw 0x16b291d105ec4fa0 0xb416b291d105ec4f 0x1ff001f007fc0704 0x101ff001f007fc07

def z405 : W := mkw 0x60142004406cdba0 0x1060142004406cdb 0xe006300440ffffd8 0xb0e006300440ffff

def z406 : W := mkw 0xe0056806e0019001 0x0ae0056806e00190 0xe007c00ff801c0fb 0x6fe007c00ff801c0

def z407 : W := mkw 0x0008020808022000 0x0000080208080220 0x00083e0000023800 0x8000083e00000238

def z408 : W := mkw 0x1d40000000000000 0x051d400000000000 0x1ff0000000000004 0x001ff00000000000

def z409 : W := mkw 0x9440000324800002 0x0e94400003248000 0x0000000380000002 0x0c00000003800000

def z410 : W := mkw 0xc9853ca000000000 0x0bc9853ca0000000 0xf98ffff0000000f7 0x8ff98ffff0000000

def z411 : W := mkw 0x0088109801060d80 0x000088109801060d 0x198831f8471e3fbc 0xd0198831f8471e3f

def z412 : W := mkw 0x098014b013140dc0 0x41098014b013140d 0x198031f0471e3f9c 0x90198031f0471e3f

def z413 : W := mkw 0x2010000440480000 0x0020100004404800 0xe1f00000401c0080 0x00e1f00000401c00

def z414 : W := mkw 0xff8fffffffb7ffc1 0x6fff8fffffffb7ff 0xff8fffffffffffff 0xffff8fffffffffff

def z415 : W := mkw 0x0000020008002000 0x0000000200080020 0x00003e0078003881 0x0300003e00780038

def z416 : W := mkw 0xf45d6a0feccbb003 0x0ef45d6a0feccbb0 0xe67ffe0ff8e3f8fb 0xefe67ffe0ff8e3f8

def z417 : W := mkw 0x9d40000336900002 0x0f9d400003369000 0x1e00000fbfe0007f 0x7f1e00000fbfe000

def z418 : W := mkw 0xe98d3ebe7b16bdc1 0x4be98d3ebe7b16bd 0xf9883ff87f1e3fbd 0xd3f9883ff87f1e3f

def z419 : W := mkw 0x20100004406cdba0 0x1020100004406cdb 0xe7f0000440ffffdc 0x30e7f0000440ffff

def z420 : W := mkw 0xbdd016a77edc29c2 0x4fbdd016a77edc29 0xfff03e0ffffc38ff 0x7ffff03e0ffffc38

def z421 : W := mkw 0xebbf7fbefb7fffe1 0xdbebbf7fbefb7fff 0xffffffffffffffff 0xffffffffffffffff

def z422 : W := mkw 0x2018401dc5efdfa0 0x302018401dc5efdf 0x0000000fc7ffff08 0x700000000fc7ffff

def z423 : W := mkw 0xa0094a0ee8032001 0x0aa0094a0ee80320 0xe009ce0ff80000fb 0x6fe009ce0ff80000

def z424 : W := mkw 0x1408401985a34600 0x241408401985a346 0x1e00000f87e3c77e 0x7c1e00000f87e3c7

def z425 : W := mkw 0x9d494a0bbe932003 0x0f9d494a0bbe9320 0x1809ce0bbf000023 0x4f1809ce0bbf0000

def z426 : W := mkw 0x1d00000116900000 0x051d000001169000 0x1f80000ffffc00ff 0x7f1f80000ffffc00

def z427 : W := mkw 0x1f0ac7799fb36640 0x651f0ac7799fb366 0x1e0fcfffbfe3c77f 0xff1e0fcfffbfe3c7

def z428 : W := mkw 0xdfe7bde000204204 0x8fdfe7bde0002042 0xfffffff400e3c7ff 0xbffffffff400e3c7

def z429 : W := mkw 0x098856b89b172dc0 0x41098856b89b172d 0x198fffffff1fffff 0xff198fffffff1fff

def z430 : W := mkw 0x76b6b1d545ecdfa0 0xb476b6b1d545ecdf 0xfff631f447ffffdc 0xb0fff631f447ffff

def z431 : W := mkw 0x098016a01a1429c0 0x41098016a01a1429 0x01803f80781e3f9d 0x9301803f80781e3f

def z432 : W := mkw 0xf40dea5fed83b401 0x2ef40dea5fed83b4 0xf80ffe7fff03f8fb 0xeff80ffe7fff03f8

def z433 : W := mkw 0x0088128808062980 0x0000881288080629 0x01883f88781e3fbd 0xd301883f88781e3f

def z434 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x0607c00f87e3c74a 0x7c0607c00f87e3c7

def z435 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x01803e087f1e3f89 0x5301803e087f1e3f

def z436 : W := mkw 0x620621044020d200 0x00620621044020d2 0xe606318440e3ffdc 0xb0e606318440e3ff

def z437 : W := mkw 0x000802181b162dc0 0x40000802181b162d 0x00083e087f1e3fb9 0xd300083e087f1e3f

def z438 : W := mkw 0xd667a94000000004 0x8ed667a940000000 0xe67ffe00000000f3 0x8fe67ffe00000000

def z439 : W := mkw 0x09e014a000000004 0x8109e014a0000000 0x01f0000000000000 0x0001f00000000000

def z440 : W := mkw 0x20901084404c0980 0x0020901084404c09 0xe7f0318440fe3fdc 0xb0e7f0318440fe3f

def z441 : W := mkw 0x000802181b162dc0 0x40000802181b162d 0x180801f87f1e3f3c 0xd0180801f87f1e3f

def z442 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x180fc1fb8703c722 0xcc180fc1fb8703c7

def z443 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x198001f87f1e3f0c 0x50198001f87f1e3f

def z444 : W := mkw 0x62362104406cdba0 0x9062362104406cdb 0xe676000440ffff48 0x30e676000440ffff

def z445 : W := mkw 0x8940000000000000 0x0b89400000000000 0xe1f0000000000081 0x03e1f00000000000

def z446 : W := mkw 0x098816a808022000 0x01098816a8080220 0x19883ff8780238bd 0xc319883ff8780238

def z447 : W := mkw 0x56a6b1c000000000 0x8456a6b1c0000000 0xfffff1f0000000f6 0x8cfffff1f0000000

def z448 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x01883ff0781e3f81 0x8301883ff0781e3f

def z449 : W := mkw 0xbd50000672580002 0x0fbd500006725800 0xfff00000781c00f7 0x0ffff00000781c00

def z450 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe00ffe078003f842 0xace00ffe078003f8

def z451 : W := mkw 0x400d6a088803b001 0x00400d6a088803b0 0x000ffe087803f8b9 0xc3000ffe087803f8

def z452 : W := mkw 0x1400805105800400 0x2414008051058004 0x1800007007000000 0x0018000070070000

def z453 : W := mkw 0x22120104406cdba0 0x1022120104406cdb 0x0606018440ffff5c 0xb00606018440ffff

def z454 : W := mkw 0x0900000012100000 0x0109000000121000 0x19800000071c0004 0x1019800000071c00

def z455 : W := mkw 0x76b6b1c4406cdba0 0x9476b6b1c4406cdb 0xfffff1f440fffffe 0xbcfffff1f440ffff

def z456 : W := mkw 0xe9f43086725c99a2 0x9be9f43086725c99 0xe1f03000781c3881 0x03e1f03000781c38

def z457 : W := mkw 0x02a2118000244ba0 0x9002a2118000244b 0x0000018000000700 0x0000000180000007

def z458 : W := mkw 0x760ee15dc5a3d600 0x24760ee15dc5a3d6 0xfe0ff1ffc7e3fffe 0xfcfe0ff1ffc7e3ff

def z459 : W := mkw 0x56aef1d985a7dfa0 0xb456aef1d985a7df 0x1e0ff1ff87e3ff7e 0xfc1e0ff1ff87e3ff

def z460 : W := mkw 0xebf73da4406cdba4 0x9bebf73da4406cdb 0xe7f63f8440ffffdd 0xb3e7f63f8440ffff

def z461 : W := mkw 0xb652c147e4e94202 0x2eb652c147e4e942 0xe677c00780e1c042 0x2ce677c00780e1c0

def z462 : W := mkw 0x1ff2118116fc4ba2 0x951ff2118116fc4b 0x1ff0018007fc0704 0x101ff0018007fc07

def z463 : W := mkw 0x9f4ac15bb7b34602 0x2f9f4ac15bb7b346 0x1e0fc1ffbfe3c77f 0xff1e0fc1ffbfe3c7

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000f8000007a 0x6c0000000f800000

def z465 : W := mkw 0x2018401ff7fb4602 0x202018401ff7fb46 0x0000000fffffc708 0x700000000fffffc7

def z466 : W := mkw 0x0008400880030000 0x0000084008800300 0x0000000f8003c008 0x600000000f8003c0

def z467 : W := mkw 0x0008001801020400 0x0000080018010204 0x000801f000020700 0x80000801f0000207

def z468 : W := mkw 0xe01d6a0ffedbb003 0x0ae01d6a0ffedbb0 0xe00ffe0ffffff8fb 0xffe00ffe0ffffff8

def z469 : W := mkw 0x1408400984830000 0x0414084009848300 0x1e0fc00f87e3c07e 0xfc1e0fc00f87e3c0

def z470 : W := mkw 0x623621044068d220 0x90623621044068d2 0xe676300440e3f8d8 0xa0e676300440e3f8

def z471 : W := mkw 0x62be338c486efba0 0x9062be338c486efb 0xe7fe3f8c78fffffd 0xf3e7fe3f8c78ffff

def z472 : W := mkw 0x9d40000000000000 0x0f9d400000000000 0x1800000000000023 0x0f18000000000000

def z473 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0x1800000ffffc002b 0x7f1800000ffffc00

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x0600000400e0005c 0x300600000400e000

def z475 : W := mkw 0x3d50000556d80002 0x053d50000556d800 0xfff0000447fc00dc 0x30fff0000447fc00

def z476 : W := mkw 0x020a011801224600 0x00020a0118012246 0x1e0e01fc07e3c77c 0xf01e0e01fc07e3c7

def z477 : W := mkw 0x1602815105a04600 0x241602815105a046 0x1e0601f407e3c75c 0xb01e0601f407e3c7

def z478 : W := mkw 0x560feb598da3f601 0x24560feb598da3f6 0x1e0fffff87e3ff7e 0xfc1e0fffff87e3ff

def z479 : W := mkw 0xe98d7eaee803b001 0x0be98d7eaee803b0 0xf98ffffff803f8ff 0xeff98ffffff803f8

def z480 : W := mkw 0xa008400ee0030000 0x0aa008400ee00300 0xe00fc00ff803c0fb 0xefe00fc00ff803c0

def z481 : W := mkw 0x0008000800020000 0x0000080008000200 0x0008000800020038 0xc000080008000200

def z482 : W := mkw 0x000802181b122440 0x40000802181b1224 0x000000083f000000 0x40000000083f0000

def z483 : W := mkw 0x623621044068d220 0x90623621044068d2 0xe7f6000440fdc0dc 0x30e7f6000440fdc0

def z484 : W := mkw 0xd60fe95985a34600 0x2ed60fe95985a346 0xfe0fffff87e3c7ff 0xfffe0fffff87e3c7

def z485 : W := mkw 0x298856befb17bdc1 0x41298856befb17bd 0x19883fffff1fffbd 0xf319883fffff1fff

def z486 : W := mkw 0xa9d816be7b5e2dc2 0x4ba9d816be7b5e2d 0xf9f83ff87f1e3fbd 0xd3f9f83ff87f1e3f

def z487 : W := mkw 0x9d40000336900002 0x0f9d400003369000 0xfff0000bbf0000f7 0x4ffff0000bbf0000

def z488 : W := mkw 0x1f8a97f81b162dc0 0x451f8a97f81b162d 0x1f8ffff87f1e3fff 0xdf1f8ffff87f1e3f

def z489 : W := mkw 0x9409ca5bad832401 0x2e9409ca5bad8324 0x1809ce7bbf000023 0x4f1809ce7bbf0000

def z490 : W := mkw 0xc2a7bde000000004 0x8ac2a7bde0000000 0xe00ffff0000000f3 0x8fe00ffff0000000

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000008780000b9 0x4300000008780000

def z492 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x19883ff0071e3f04 0x9019883ff0071e3f

def z493 : W := mkw 0xbd58420ffedbb003 0x0fbd58420ffedbb0 0xfff0000ffffff8ff 0x7ffff0000ffffff8

def z494 : W := mkw 0x4226210000000000 0x8042262100000000 0xe676000000000040 0x00e6760000000000

def z495 : W := mkw 0x4ba7bde000000004 0x814ba7bde0000000 0x198ffff0000000b5 0x83198ffff0000000

def z496 : W := mkw 0xfff7bde440480004 0x8ffff7bde4404800 0xfffffff440fc00ff 0xbffffffff440fc00

def z497 : W := mkw 0x89895ebabb172dc1 0x4b89895ebabb172d 0x1989fffbff1e3fbf 0xdf1989fffbff1e3f

def z498 : W := mkw 0x60b43084404c99a0 0x9060b43084404c99 0xe1f03180401e3f9c 0x90e1f03180401e3f

def z499 : W := mkw 0x0000000104800000 0x0000000001048000 0x0000000f87e00008 0x700000000f87e000

def z500 : W := mkw 0x1408c05985a34600 0x241408c05985a346 0x1809c07f87e3c72a 0x7c1809c07f87e3c7

def z501 : W := mkw 0xc065280000000004 0x8ac0652800000000 0xe070000000000000 0x00e0700000000000

def z502 : W := mkw 0x0008420aa8032001 0x000008420aa80320 0x0000000bb8000000 0x400000000bb80000

def z503 : W := mkw 0xe00d680ee0039001 0x0ae00d680ee00390 0xe00fc00f8003c07a 0xece00fc00f8003c0

def z504 : W := mkw 0x1d50000116d80002 0x051d50000116d800 0x1ff000087ffc00bd 0x531ff000087ffc00

def z505 : W := mkw 0x40a53ca000000004 0x8040a53ca0000000 0x00003e0000000000 0x0000003e00000000

def z506 : W := mkw 0xffefffffeda3f605 0xafffefffffeda3f6 0xffffffffffe3ffff 0xffffffffffffe3ff

def z507 : W := mkw 0xf607e947e4a1d201 0x2ef607e947e4a1d2 0xe607c00780e1c042 0x2ce607c00780e1c0

def z508 : W := mkw 0xe9f53ca4404c99a4 0x9be9f53ca4404c99 0xe1f03e00401c3881 0x03e1f03e00401c38

def z509 : W := mkw 0x9d50000116d80002 0x0f9d50000116d800 0xfff0000007fc00f7 0x1ffff0000007fc00

def z510 : W := mkw 0xa950000672580002 0x0ba9500006725800 0xe7f0000478fc00dd 0x33e7f0000478fc00

def z511 : W := mkw 0xdfeffdf985830404 0xafdfeffdf9858304 0xfffffffb870000f7 0xcffffffffb870000

def z512 : W := mkw 0xe2b63186606cdba0 0x9ae2b63186606cdb 0xe7f6318ff8ffffff 0xffe7f6318ff8ffff

def z513 : W := mkw 0x7ff6b5e4406cdba4 0x957ff6b5e4406cdb 0xfff631f440ffffdc 0xb0fff631f440ffff

def z514 : W := mkw 0x0202815001204600 0x2002028150012046 0x000001f000000700 0x00000001f0000007

def z515 : W := mkw 0x2000000440009000 0x0020000004400090 0x000000044003f808 0x20000000044003f8

def z516 : W := mkw 0xe08d7ebee907bdc1 0x4ae08d7ebee907bd 0xe00ffffff803fffb 0xefe00ffffff803ff

def z517 : W := mkw 0x299816bc5b7effe0 0x51299816bc5b7eff 0x19883ffc7fffffbd 0xf319883ffc7fffff

def z518 : W := mkw 0x1fe295e000000004 0x851fe295e0000000 0x1ff83ff0000000b5 0x831ff83ff0000000

def z519 : W := mkw 0x1d8816b91f962dc0 0x451d8816b91f962d 0x1f883ffffffe3fff 0xff1f883ffffffe3f

def z520 : W := mkw 0x1400000104800000 0x0414000001048000 0x0600000780e00042 0x2c0600000780e000

def z521 : W := mkw 0x80094a0aa8032001 0x0a80094a0aa80320 0x000fce0fb803c07b 0xef000fce0fb803c0

def z522 : W := mkw 0x9d49cc7985830404 0x2f9d49cc79858304 0x1809ce7b87000023 0x4f1809ce7b870000

def z523 : W := mkw 0xf667e946e0019005 0x8ef667e946e00190 0xe677c0078001c042 0x2ce677c0078001c0

def z524 : W := mkw 0x0008401881234600 0x2000084018812346 0x000000000003c700 0x00000000000003c7

def z525 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e09c1fb87e00726 0x5c1e09c1fb87e007

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000080700003c 0x5018000008070000

def z527 : W := mkw 0x0080108000040980 0x0000801080000409 0x01800180001c0704 0x1001800180001c07

def z528 : W := mkw 0xa9d016a67a5c29c2 0x4ba9d016a67a5c29 0xe1f03e00781c3881 0x03e1f03e00781c38

def z529 : W := mkw 0xbd58021f7fde2dc2 0x4fbd58021f7fde2d 0xfff0000ffffe3fff 0x7ffff0000ffffe3f

def z530 : W := mkw 0x2008420ee803b001 0x002008420ee803b0 0x00083e0ff803f8b9 0xe300083e0ff803f8

def z531 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xf9f0000bff1c00a3 0x4ff9f0000bff1c00

def z532 : W := mkw 0x600c220c4802b000 0x00600c220c4802b0 0xe00e3e0c7803f8f9 0xe3e00e3e0c7803f8

def z533 : W := mkw 0x0000001013140dc0 0x400000001013140d 0x00000000071c0700 0x1000000000071c07

def z534 : W := mkw 0x62b63184404c99a0 0x9062b63184404c99 0xe7f63180401c38d4 0x80e7f63180401c38

def z535 : W := mkw 0xe9ed7eaee803b005 0x8be9ed7eaee803b0 0xe1fffe0ff803f8fb 0xefe1fffe0ff803f8

def z536 : W := mkw 0x000000000024dba0 0x10000000000024db 0x000000000003ff00 0x00000000000003ff

def z537 : W := mkw 0x098014a000000000 0x01098014a0000000 0x01803e0000000081 0x0301803e00000000

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x00083e00000000b1 0x8300083e00000000

def z539 : W := mkw 0xdfe7bdf013140dc4 0xcfdfe7bdf013140d 0xfffffff0071c07f7 0x9ffffffff0071c07

def z540 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f0318040fc3f84 0x10e7f0318040fc3f

def z541 : W := mkw 0x9f42814000000000 0x0f9f428140000000 0xffffc1f0000000f7 0x8fffffc1f0000000

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0x180801f000000034 0x80180801f0000000

def z543 : W := mkw 0x098014a000000000 0x01098014a0000000 0x198001f000000004 0x00198001f0000000

def z544 : W := mkw 0xfff7bde776fcdba6 0x9ffff7bde776fcdb 0xffffffffffffffff 0xffffffffffffffff

def z545 : W := mkw 0x160ac15985830400 0x24160ac159858304 0x1e0fc1fb87000076 0xcc1e0fc1fb870000

def z546 : W := mkw 0x62be319c416edfa0 0x9062be319c416edf 0xfffe31fc47fffffc 0xf0fffe31fc47ffff

def z547 : W := mkw 0xdd45ac6000000004 0x0fdd45ac60000000 0xf80ffe70000000f3 0x8ff80ffe70000000

def z548 : W := mkw 0x2010000440480000 0x0020100004404800 0xe670000400e00040 0x20e670000400e000

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0x000600040003c058 0xa0000600040003c0

def z550 : W := mkw 0x1d40846000000004 0x051d408460000000 0x1800007000000000 0x0018000070000000

def z551 : W := mkw 0x42a631800024dba0 0x9042a631800024db 0xe7f631800003ffd4 0x80e7f631800003ff

def z552 : W := mkw 0x1400000104800000 0x0414000001048000 0x1e00000007e00004 0x101e00000007e000

def z553 : W := mkw 0x098814b813160dc0 0x41098814b813160d 0x198801f8071e073c 0xd0198801f8071e07

def z554 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x18083ff83f023f21 0xc318083ff83f023f

def z555 : W := mkw 0xf4556807e4c99003 0x0ef4556807e4c990 0xe677c00780e1c042 0x2ce677c00780e1c0

def z556 : W := mkw 0x090806381b122440 0x41090806381b1224 0x18080ff83f02073d 0xd318080ff83f0207

def z557 : W := mkw 0xe20feb5ee923f601 0x2ae20feb5ee923f6 0xe00ffffff803fffb 0xefe00ffffff803ff

def z558 : W := mkw 0x0000001105a04600 0x200000001105a046 0x0000000007e00700 0x100000000007e007

def z559 : W := mkw 0x098816b81b122440 0x41098816b81b1224 0x19883ff83f0000b5 0xc319883ff83f0000

def z560 : W := mkw 0xdfefbff81b122444 0xcfdfefbff81b1224 0xfffffff83f0000f7 0xcffffffff83f0000

def z561 : W := mkw 0x0008401985a34600 0x200008401985a346 0x180801ff87e3c73c 0xf0180801ff87e3c7

def z562 : W := mkw 0x2910000776d80002 0x012910000776d800 0x1980000ffffc00bd 0x731980000ffffc00

def z563 : W := mkw 0x090006201a102040 0x41090006201a1020 0x00000e0038000001 0x0300000e00380000

def z564 : W := mkw 0x0008020808022000 0x0000080208080220 0x00080e0838000021 0x4300080e08380000

def z565 : W := mkw 0x62be339c5b7effe0 0xd062be339c5b7eff 0xe7f6318c7fffffdc 0xf0e7f6318c7fffff

def z566 : W := mkw 0xe0052a066800b001 0x0ae0052a066800b0 0xe0003e0ff80038fb 0x6fe0003e0ff80038

def z567 : W := mkw 0x098014b013140dc0 0x41098014b013140d 0x198001f87f1c07bd 0x53198001f87f1c07

def z568 : W := mkw 0xbd58401ff7fb4602 0x2fbd58401ff7fb46 0xfff0000fffffc7ff 0x7ffff0000fffffc7

def z569 : W := mkw 0x9d49ce6aa8032005 0x0f9d49ce6aa80320 0x1809ce7bb8000023 0x4f1809ce7bb80000

def z570 : W := mkw 0xe005280660009001 0x0ae0052806600090 0xe000000000000000 0x00e0000000000000

def z571 : W := mkw 0x0080108000040980 0x0000801080000409 0x01803000401c3880 0x0001803000401c38

def z572 : W := mkw 0x0000000000040980 0x0000000000000409 0x00000000401e3f08 0x1000000000401e3f

def z573 : W := mkw 0x008816b809062dc0 0x40008816b809062d 0x18083ff807023f3c 0xd018083ff807023f

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x01800000401c009c 0x1001800000401c00

def z575 : W := mkw 0x0008401881030400 0x0000084018810304 0x180fc1ff8703c77e 0xfc180fc1ff8703c7

def z576 : W := mkw 0xf677a9444068d224 0x9ef677a9444068d2 0xe677c00400e1c042 0x2ce677c00400e1c0

def z577 : W := mkw 0x1400000000000000 0x0414000000000000 0x1e00000000000076 0x0c1e000000000000

def z578 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfff03ff000000085 0x03fff03ff0000000

def z579 : W := mkw 0x9dc99ef81b162dc4 0x4f9dc99ef81b162d 0x1989fff87f1e3fbf 0xdf1989fff87f1e3f

def z580 : W := mkw 0x160a815905a24600 0x24160a815905a246 0x1e0801f807e2073c 0xd01e0801f807e207

def z581 : W := mkw 0x2212010440684200 0x0022120104406842 0xe7f6018440ffc7dc 0xb0e7f6018440ffc7

def z582 : W := mkw 0xa050000660480002 0x0aa0500006604800 0xe070000000000000 0x00e0700000000000

def z583 : W := mkw 0x42afbff809062dc4 0xc042afbff809062d 0x000ffff000023f00 0x80000ffff000023f

def z584 : W := mkw 0x00100000006c4ba0 0x1000100000006c4b 0x0000000000fc0700 0x100000000000fc07

def z585 : W := mkw 0xffffffeffedbb007 0x8fffffffeffedbb0 0xfffffffffffff8ff 0xfffffffffffffff8

def z586 : W := mkw 0xe90d6a0efa13b001 0x0be90d6a0efa13b0 0xf98ffe0fff1ff8ff 0xfff98ffe0fff1ff8

def z587 : W := mkw 0xd667e94184a14204 0xaed667e94184a142 0xe677c00780e1c042 0x2ce677c00780e1c0

def z588 : W := mkw 0x56aef1d985a34600 0xa456aef1d985a346 0xfffff1ff87e3c7fe 0xfcfffff1ff87e3c7

def z589 : W := mkw 0xbdd014a776d80002 0x0fbdd014a776d800 0xfff83ffffffc00ff 0xfffff83ffffffc00

def z590 : W := mkw 0x1602814000000000 0x0416028140000000 0x0607c00000000042 0x0c0607c000000000

def z591 : W := mkw 0x80014802a0010001 0x0a80014802a00100 0x0001c00380000002 0x0c0001c003800000

def z592 : W := mkw 0xe0056806e0019001 0x0ae0056806e00190 0xe007f007c003f8da 0xace007f007c003f8

def z593 : W := mkw 0x020ac15881234600 0x20020ac158812346 0x060fc1f400e3c75c 0xb0060fc1f400e3c7

def z594 : W := mkw 0xffeffffefb17bdc5 0xcfffeffffefb17bd 0xffffffffff1fffff 0xffffffffffff1fff

def z595 : W := mkw 0x0202814000000000 0x0002028140000000 0x000fc1f000000000 0x80000fc1f0000000

def z596 : W := mkw 0xfd54200776d89002 0x0ffd54200776d890 0xfff6300ffffff8ff 0xfffff6300ffffff8

def z597 : W := mkw 0x9d40000012100000 0x0f9d400000121000 0xfff000087f1c00ff 0x5ffff000087f1c00

def z598 : W := mkw 0xfd4dee6ee803b005 0x0ffd4dee6ee803b0 0xf80ffe7ff803f8fb 0xeff80ffe7ff803f8

def z599 : W := mkw 0x020a410880234200 0x00020a4108802342 0x060fc18f80e3c77e 0xfc060fc18f80e3c7

def z600 : W := mkw 0xe2b77986e06ddba1 0x9ae2b77986e06ddb 0xe7f7f187c0ffffde 0xbce7f7f187c0ffff

def z601 : W := mkw 0xfff7bde672580006 0x8ffff7bde6725800 0xfffffff0781c00f7 0x8ffffffff0781c00

def z602 : W := mkw 0x1408c05985830400 0x241408c059858304 0x1e09c07f87e0007e 0x7c1e09c07f87e000

def z603 : W := mkw 0x16bad1d985ef4fa0 0xb416bad1d985ef4f 0x1fffc1ff87ffc77e 0xfc1fffc1ff87ffc7

def z604 : W := mkw 0xc005280000000000 0x0ac0052800000000 0xe007c00000000042 0x0ce007c000000000

def z605 : W := mkw 0x1d88d6f99f972dc0 0x651d88d6f99f972d 0x1989fffbff1e3fbf 0xdf1989fffbff1e3f

def z606 : W := mkw 0x000002001a1429c0 0x40000002001a1429 0x00000000781c3800 0x0000000000781c38

def z607 : W := mkw 0xffe7fde6e0019005 0x8fffe7fde6e00190 0xfffffff78001c0f7 0xaffffffff78001c0

def z608 : W := mkw 0xa950000776d80002 0x0ba950000776d800 0xe1f0000ffffc0089 0x73e1f0000ffffc00

def z609 : W := mkw 0x090806381b122440 0x41090806381b1224 0x18083e787f0238b9 0xc318083e787f0238

def z610 : W := mkw 0x1dd816b91fde2dc2 0x451dd816b91fde2d 0x1ff83ff87ffe3fbd 0xd31ff83ff87ffe3f

def z611 : W := mkw 0x6034200440489020 0x9060342004404890 0xe070000000000000 0x00e0700000000000

def z612 : W := mkw 0xe98d7eaefa17b9c1 0x4be98d7eaefa17b9 0xe18ffe0ff81ff8fb 0xefe18ffe0ff81ff8

def z613 : W := mkw 0xfd556807f6d99003 0x0ffd556807f6d990 0xfff7c00ffffdc0ff 0x7ffff7c00ffffdc0

def z614 : W := mkw 0xfd4d6a0ffe93b003 0x0ffd4d6a0ffe93b0 0xf80ffe0fff03f8fb 0xeff80ffe0fff03f8

def z615 : W := mkw 0xe005280440009000 0x0ae0052804400090 0xe00ffe044003f8fb 0xafe00ffe044003f8

def z616 : W := mkw 0x42b63180006cdba0 0x9042b63180006cdb 0x07f6318000ffff04 0x9007f6318000ffff

def z617 : W := mkw 0x62bf7b8cc86ffba1 0x9062bf7b8cc86ffb 0xe7ffff8440ffffdc 0xb0e7ffff8440ffff

def z618 : W := mkw 0x00094a0888032001 0x0000094a08880320 0x0009ce0000000000 0x000009ce00000000

def z619 : W := mkw 0x020ac15985a34600 0x20020ac15985a346 0x000fc1ff87e3c708 0xf0000fc1ff87e3c7

def z620 : W := mkw 0xe00d2a0e6802b001 0x0ae00d2a0e6802b0 0xe0083e08780238b9 0xc3e0083e08780238

def z621 : W := mkw 0x0202010000204200 0x0002020100002042 0x000601800003c700 0x80000601800003c7

def z622 : W := mkw 0x008816b809062dc0 0x40008816b809062d 0x01883ff0401e3f9c 0x9001883ff0401e3f

def z623 : W := mkw 0x9fe295e000000004 0x8f9fe295e0000000 0xfff001f0000000f7 0x0ffff001f0000000

def z624 : W := mkw 0x098014b013140dc0 0x41098014b013140d 0x19883ff0071c07b5 0x9319883ff0071c07

def z625 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x060fc1f780e3c742 0xac060fc1f780e3c7

def z626 : W := mkw 0xe9853ea67a14b9c1 0x4be9853ea67a14b9 0xe1803e00781c3881 0x03e1803e00781c38

def z627 : W := mkw 0x02b21180006c4ba0 0x9002b21180006c4b 0x07f0318040fe3f9c 0x9007f0318040fe3f

def z628 : W := mkw 0xf6bffbdfedefffa1 0xbef6bffbdfedefff 0xffffffffffffffff 0xffffffffffffffff

def z629 : W := mkw 0x1f52815117f84602 0x251f52815117f846 0x1ff001f007fc0704 0x101ff001f007fc07

def z630 : W := mkw 0x098816a81a1629c0 0x41098816a81a1629 0x01883e08781e38b9 0xc301883e08781e38

def z631 : W := mkw 0x6014200440489000 0x0060142004404890 0xe7f6300440fff8dc 0xb0e7f6300440fff8

def z632 : W := mkw 0x000842199fb76fc0 0x60000842199fb76f 0x0000000fffffff08 0x700000000fffffff

def z633 : W := mkw 0xdfe6318000000000 0x8fdfe63180000000 0xfff63180000000f7 0x8ffff63180000000

def z634 : W := mkw 0x0008401985a34600 0x200008401985a346 0x000fc00f87e3c77a 0xfc000fc00f87e3c7

def z635 : W := mkw 0x1fe295f013140dc4 0xc51fe295f013140d 0x1ff001f0071c0704 0x101ff001f0071c07

def z636 : W := mkw 0xd66fe95985a34604 0xaed66fe95985a346 0xfe7fc1ff87e3c77e 0xfcfe7fc1ff87e3c7

def z637 : W := mkw 0xffffffeee86ffba5 0x9fffffffeee86ffb 0xfffffffff8ffffff 0xfffffffffff8ffff

def z638 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0001ff87e3c70c 0x701e0001ff87e3c7

def z639 : W := mkw 0xfddd7ebfffdfbdc3 0x4ffddd7ebfffdfbd 0xffffffffffffffff 0xffffffffffffffff

def z640 : W := mkw 0xe00d6a1efb17bdc1 0x4ae00d6a1efb17bd 0xe00ffe0fff1ffffb 0xffe00ffe0fff1fff

def z641 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe676318400e3ff40 0xa0e676318400e3ff

def z642 : W := mkw 0x200002066800b001 0x00200002066800b0 0x0000000078003800 0x0000000000780038

def z643 : W := mkw 0x62be718cc06fdba0 0x9062be718cc06fdb 0xe7fff18fc0fffffe 0xfce7fff18fc0ffff

def z644 : W := mkw 0xf676210764e8d222 0x9ef676210764e8d2 0xe676000780e1c042 0x2ce676000780e1c0

def z645 : W := mkw 0xffe7bde660000004 0x8fffe7bde6600000 0xfffffffff80000ff 0xeffffffffff80000

def z646 : W := mkw 0x8940000232100002 0x0b89400002321000 0x0000000038000001 0x0300000000380000

def z647 : W := mkw 0xbd58c05ff7db0402 0x2fbd58c05ff7db04 0xfff9c07ffffc00ff 0x7ffff9c07ffffc00

def z648 : W := mkw 0x2000000440000000 0x0020000004400000 0xe0000004400000d8 0x20e0000004400000

def z649 : W := mkw 0x0202010000204200 0x0002020100002042 0x0606000400e1c040 0x200606000400e1c0

def z650 : W := mkw 0x2008421efb17bdc1 0x402008421efb17bd 0x0000000fff1fff08 0x700000000fff1fff

def z651 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe009fe0bf80038a3 0x4fe009fe0bf80038

def z652 : W := mkw 0xe005280660000000 0x0ae0052806600000 0xe00ffe0ff80000fb 0xefe00ffe0ff80000

def z653 : W := mkw 0xbf52c147f6f94202 0x2fbf52c147f6f942 0xfff7c00ffffdc0ff 0x7ffff7c00ffffdc0

def z654 : W := mkw 0xffffbffc5b7effe4 0xdfffffbffc5b7eff 0xfffffffc7fffffff 0xfffffffffc7fffff

def z655 : W := mkw 0xd6e7b9c000000004 0x8ed6e7b9c0000000 0xe7f7f180000000d6 0x8ce7f7f180000000

def z656 : W := mkw 0x1f8ad5f997b74fc0 0x651f8ad5f997b74f 0x1f8fc1ff87ffc77e 0xfc1f8fc1ff87ffc7

def z657 : W := mkw 0x4227a94000000004 0x804227a940000000 0x0007c00000000000 0x000007c000000000

def z658 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6018400fdc744 0x30e7f6018400fdc7

def z659 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x19880ff83f1c0725 0x5319880ff83f1c07

def z660 : W := mkw 0xb60ac15fe5a34600 0x2eb60ac15fe5a346 0xfe0fc1ffffe3c7ff 0xfffe0fc1ffffe3c7

def z661 : W := mkw 0x1400804000000000 0x0414008040000000 0x1809c07000000022 0x0c1809c070000000

def z662 : W := mkw 0xfff7bde44068d224 0x9ffff7bde44068d2 0xfffffff400e1c0f7 0xaffffffff400e1c0

def z663 : W := mkw 0x020ac15881234600 0x20020ac158812346 0x180fc1f80703c73c 0xd0180fc1f80703c7

def z664 : W := mkw 0x361ac15dc5eb4600 0x24361ac15dc5eb46 0xffffc1ffc7ffc7fe 0xfcffffc1ffc7ffc7

def z665 : W := mkw 0x42a6318000000000 0x8042a63180000000 0x0006318000000000 0x8000063180000000

def z666 : W := mkw 0x2018021f7fde2dc2 0x402018021f7fde2d 0x0000000ffffe3f08 0x700000000ffffe3f

def z667 : W := mkw 0x0202010000000000 0x0002020100000000 0x0606018000000054 0x8006060180000000

def z668 : W := mkw 0xbd58400ff6db0002 0x0fbd58400ff6db00 0xffffc00fffffc0ff 0xffffffc00fffffc0

def z669 : W := mkw 0x098014a000040980 0x01098014a0000409 0x19883ff0401e3fbd 0x9319883ff0401e3f

def z670 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0fc1f007e3c704 0x901e0fc1f007e3c7

def z671 : W := mkw 0x9d48063b3f922442 0x4f9d48063b3f9224 0x18080e7bbf000023 0x4f18080e7bbf0000

def z672 : W := mkw 0x40a43080000499a0 0x9040a43080000499 0x0000300000003800 0x0000003000000038

def z673 : W := mkw 0x299816bf7fde2dc2 0x41299816bf7fde2d 0x19883ffffffe3fbd 0xf319883ffffffe3f

def z674 : W := mkw 0x0008c05881030400 0x200008c058810304 0x0009c07000000000 0x000009c070000000

def z675 : W := mkw 0xe01d6a0ee86ffba1 0x1ae01d6a0ee86ffb 0xe00ffe0ff8fffffb 0xffe00ffe0ff8ffff

def z676 : W := mkw 0xdfefbdf801020404 0x8fdfefbdf8010204 0xfffffff8070207ff 0xdffffffff8070207

def z677 : W := mkw 0x0008400880030000 0x0000084008800300 0x0009c00b80000022 0x4c0009c00b800000

def z678 : W := mkw 0x62b631844068d220 0x9062b631844068d2 0xe7f6318400e1c0d4 0xa0e7f6318400e1c0

def z679 : W := mkw 0xff5feb5ffffbf603 0x2fff5feb5ffffbf6 0xffffffffffffffff 0xffffffffffffffff

def z680 : W := mkw 0xbff295e776d80006 0x8fbff295e776d800 0xfff001fffffc00ff 0x7ffff001fffffc00

def z681 : W := mkw 0x76b6f1c5c4eddba0 0xb476b6f1c5c4eddb 0xe7f7f187c0ffffde 0xbce7f7f187c0ffff

def z682 : W := mkw 0x9fe39de000000004 0x8f9fe39de0000000 0x1ff9cff000000027 0x0f1ff9cff0000000

def z683 : W := mkw 0x2018021c5b7effe0 0x502018021c5b7eff 0x0000000c7fffff08 0x700000000c7fffff

def z684 : W := mkw 0xff76210776f8d222 0x9fff76210776f8d2 0xfff6000ffffdc0ff 0x7ffff6000ffffdc0

def z685 : W := mkw 0x098016a01a1429c0 0x41098016a01a1429 0x19803e087f1c38bd 0x5319803e087f1c38

def z686 : W := mkw 0x9441884000000004 0x0e94418840000000 0x0001c00000000002 0x0c0001c000000000

def z687 : W := mkw 0x1662814000000004 0x8416628140000000 0x0670000000000000 0x0006700000000000

def z688 : W := mkw 0x1602814000204200 0x0416028140002042 0x1e0fc1f400e3c77e 0xbc1e0fc1f400e3c7

def z689 : W := mkw 0x361ac15dc5efdfa0 0x34361ac15dc5efdf 0x1e0fc1ffc7ffff7e 0xfc1e0fc1ffc7ffff

def z690 : W := mkw 0x020a411985a34600 0x20020a411985a346 0x0606018f87e3c75c 0xf00606018f87e3c7

def z691 : W := mkw 0xfff63184406cdba0 0x9ffff63184406cdb 0xfff6318440ffffff 0xbffff6318440ffff

def z692 : W := mkw 0x1450000104c80002 0x041450000104c800 0x0670000000e00000 0x000670000000e000

def z693 : W := mkw 0x6bb635a4406cdba0 0x916bb635a4406cdb 0xfffe3ff440fffffd 0xb3fffe3ff440ffff

def z694 : W := mkw 0xbd50000764c80002 0x0fbd50000764c800 0xfff0000780e000f7 0x2ffff0000780e000

def z695 : W := mkw 0x40052a000800b001 0x0040052a000800b0 0x00003e0000003800 0x0000003e00000038

def z696 : W := mkw 0xdfe7bdf105a04604 0xafdfe7bdf105a046 0xfffffff007e007f7 0x9ffffffff007e007

def z697 : W := mkw 0x2010000440480000 0x0020100004404800 0x0000000440fc0008 0x300000000440fc00

def z698 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xe7f00007f8fc00c3 0x2fe7f00007f8fc00

def z699 : W := mkw 0x1408001905820400 0x0414080019058204 0x1e0801ff87e2077e 0xfc1e0801ff87e207

def z700 : W := mkw 0x098016a01a1429c0 0x41098016a01a1429 0x19883ff0781c38b5 0x8319883ff0781c38

def z701 : W := mkw 0xe2af7b8ee827fba1 0x9ae2af7b8ee827fb 0xe00fff8ff803fffb 0xefe00fff8ff803ff

def z702 : W := mkw 0x2000000660000000 0x0020000006600000 0x0000000ff8000008 0x600000000ff80000

def z703 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe007c00ff803f84a 0x6ce007c00ff803f8

def z704 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x19883e787f1c38a1 0x4319883e787f1c38

def z705 : W := mkw 0x090806381b162dc0 0x41090806381b162d 0x18080e787f1e3f29 0x5318080e787f1e3f

def z706 : W := mkw 0x008816b809062dc0 0x40008816b809062d 0x00083ff878023fb9 0xc300083ff878023f

def z707 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xe7fffff0000000c3 0x8fe7fffff0000000

def z708 : W := mkw 0x60943084404c9980 0x0060943084404c99 0xe7f6318440ffffdc 0xb0e7f6318440ffff

def z709 : W := mkw 0xf607ab576da0f601 0x2ef607ab576da0f6 0xfe003ff07fe03f85 0x13fe003ff07fe03f

def z710 : W := mkw 0x62b6b5e4406cdba4 0x9062b6b5e4406cdb 0xe7f631f440ffffdc 0xb0e7f631f440ffff

def z711 : W := mkw 0x400d6a088803b001 0x00400d6a088803b0 0x000ffe0ff803f8fb 0xef000ffe0ff803f8

def z712 : W := mkw 0xd6e7bde000000004 0x8ed6e7bde0000000 0xfe7ffff000000076 0x8cfe7ffff0000000

def z713 : W := mkw 0x9d494e3bbf932443 0x4f9d494e3bbf9324 0x1809ce7bbf000023 0x4f1809ce7bbf0000

def z714 : W := mkw 0xdfe7bde000009004 0x8fdfe7bde0000090 0xfffffff00003f8f7 0x8ffffffff00003f8

def z715 : W := mkw 0xbd518c64406cdba4 0x1fbd518c64406cdb 0x1809ce7440ffff2b 0x3f1809ce7440ffff

def z716 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0fc1f787e3c746 0xbc1e0fc1f787e3c7

def z717 : W := mkw 0xcba73da000000000 0x8bcba73da0000000 0xfffffff0000000f7 0x8ffffffff0000000

def z718 : W := mkw 0xdfe7bde336900006 0x8fdfe7bde3369000 0xfffffffbff1c00ff 0xdffffffffbff1c00

def z719 : W := mkw 0xe01d6a0ee84bb001 0x0ae01d6a0ee84bb0 0xe1fffe0ff81ff8fb 0xefe1fffe0ff81ff8

def z720 : W := mkw 0xc2a7bde000000004 0x8ac2a7bde0000000 0xe7fffff0000000f7 0x8fe7fffff0000000

def z721 : W := mkw 0x5d5d6a099edbb003 0x055d5d6a099edbb0 0x1ffffe0007fff804 0x901ffffe0007fff8

def z722 : W := mkw 0x9dc19ce000000004 0x0f9dc19ce0000000 0xfff9fff0000000f7 0x8ffff9fff0000000

def z723 : W := mkw 0x74bcf0ddc5cf9da0 0xb474bcf0ddc5cf9d 0xf9f9f07bc71c38a2 0x4cf9f9f07bc71c38

def z724 : W := mkw 0x098016b01b142dc0 0x41098016b01b142d 0x19803ff87f1c3fbd 0x5319803ff87f1c3f

def z725 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xfffe31f440fffffc 0xb0fffe31f440ffff

def z726 : W := mkw 0xdf67ad6000000004 0x8fdf67ad60000000 0xfe7fcff000000077 0x8ffe7fcff0000000

def z727 : W := mkw 0xc9e53ca000000004 0x8bc9e53ca0000000 0xf9fffff0000000f7 0x8ff9fffff0000000

def z728 : W := mkw 0xe9857cb6f3159dc1 0x4be9857cb6f3159d 0xf987c1f7871dc746 0x3cf987c1f7871dc7

def z729 : W := mkw 0xdfe6318336b4dba2 0x9fdfe6318336b4db 0x1806318bbf03ff23 0xcf1806318bbf03ff

def z730 : W := mkw 0x42aef7f88927ffe0 0xf042aef7f88927ff 0x000ffff00003ff00 0x80000ffff00003ff

def z731 : W := mkw 0x2008420ee803b001 0x002008420ee803b0 0x000ffe0ff803f8fb 0xef000ffe0ff803f8

def z732 : W := mkw 0xab5ac15ef37b4602 0x2bab5ac15ef37b46 0xe1ffc1f0781fc781 0x83e1ffc1f0781fc7

def z733 : W := mkw 0x3d50000776d80002 0x053d50000776d800 0xfff0000ffffc00dc 0x70fff0000ffffc00

def z734 : W := mkw 0x6b3e273c5b7af660 0xd16b3e273c5b7af6 0xfe7e0e7c3fe1c061 0x63fe7e0e7c3fe1c0

def z735 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7fe3f8440fffffd 0xb3e7fe3f8440ffff

def z736 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfe7ffff000000063 0x8ffe7ffff0000000

def z737 : W := mkw 0xdf47a94000000000 0x0fdf47a940000000 0xfffffff0000000f7 0x8ffffffff0000000

def z738 : W := mkw 0xc9ed7cb985a34604 0xabc9ed7cb985a346 0xe1f03e0f87e3c789 0x73e1f03e0f87e3c7

def z739 : W := mkw 0xd66fab581b162dc4 0xced66fab581b162d 0xe677c0087f1e3f4a 0x5ce677c0087f1e3f

def z740 : W := mkw 0x0008401985a34600 0x200008401985a346 0x180fc1ff87e3c77e 0xfc180fc1ff87e3c7

def z741 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff0000fbffc0067 0x7ffff0000fbffc00

def z742 : W := mkw 0x3fead7eee803b005 0x853fead7eee803b0 0x1ff001fff803f80c 0x601ff001fff803f8

def z743 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6318440ffffc0 0xa0e7f6318440ffff

def z744 : W := mkw 0xdd65ac6000000004 0x8fdd65ac60000000 0xf879ce7000000023 0x0ff879ce70000000

def z745 : W := mkw 0xdfe7bde00024dba4 0x9fdfe7bde00024db 0xfffffff0401fffff 0x9ffffffff0401fff

def z746 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x19883ff07f1e3f85 0x9319883ff07f1e3f

def z747 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffe70000000e3 0x0ffffffe70000000

def z748 : W := mkw 0x9d48c67bbf932442 0x6f9d48c67bbf9324 0x1809ce7bbf000023 0x4f1809ce7bbf0000

def z749 : W := mkw 0x4ba7bde000000004 0x814ba7bde0000000 0xfffffff0000000f5 0x83fffffff0000000

def z750 : W := mkw 0x62b73da4406cdba4 0x9062b73da4406cdb 0xe7f63f8440ffffdc 0xb0e7f63f8440ffff

def z751 : W := mkw 0xdfe7bde000040984 0x8fdfe7bde0000409 0xfffffff000023ff7 0x8ffffffff000023f

def z752 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1f8fc1ffc7ffc7fe 0xfc1f8fc1ffc7ffc7

def z753 : W := mkw 0xbd50804776d80002 0x0fbd50804776d800 0xfff9c07ffffc00ff 0x7ffff9c07ffffc00

def z754 : W := mkw 0xdfe7bde220000004 0x8fdfe7bde2200000 0xfffffffbb80000f7 0xcffffffffbb80000

def z755 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0ff1ffc7e3fffe 0xfc1e0ff1ffc7e3ff

def z756 : W := mkw 0xa950000776d80002 0x0ba950000776d800 0xe7f0000ffffc00dd 0x73e7f0000ffffc00

def z757 : W := mkw 0xe06d6a0ee803b005 0x8ae06d6a0ee803b0 0xe07ffe0ff803f8fb 0xefe07ffe0ff803f8

def z758 : W := mkw 0xbd518c6776d80006 0x0fbd518c6776d800 0x1809ce7ffffc002b 0x7f1809ce7ffffc00

def z759 : W := mkw 0x62b7bde4406cdba4 0x9062b7bde4406cdb 0x000ffff440ffff08 0xb0000ffff440ffff

def z760 : W := mkw 0xdfe7bde0121409c4 0xcfdfe7bde0121409 0xfffffff0001c00f7 0x8ffffffff0001c00

def z761 : W := mkw 0xdfe7bde000204204 0x8fdfe7bde0002042 0xfffffff000e007f7 0x9ffffffff000e007

def z762 : W := mkw 0x9d40000116900000 0x0f9d400001169000 0xfff0000ffffc00ff 0x7ffff0000ffffc00

def z763 : W := mkw 0x62b7b9c4406cdba4 0x9062b7b9c4406cdb 0xe7f7f18440ffffdc 0xb0e7f7f18440ffff

def z764 : W := mkw 0x62b6b1c4406cdba0 0x9062b6b1c4406cdb 0xe7fff1f440ffffdc 0xb0e7fff1f440ffff

def z765 : W := mkw 0xdfe7bde104a04204 0x8fdfe7bde104a042 0xffffffff87e3c7ff 0xffffffffff87e3c7

def z766 : W := mkw 0xdfe7bde336900006 0x8fdfe7bde3369000 0xffffffffbfe000ff 0xffffffffffbfe000

def z767 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff0000ffffc008d 0x73fff0000ffffc00

def z768 : W := mkw 0xdde5bce000000004 0x8fdde5bce0000000 0xf9f9fff0000000b7 0x8ff9f9fff0000000

def z769 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff0401c00ff 0x9ffffffff0401c00

def z770 : W := mkw 0xe005280660009000 0x0ae0052806600090 0xe00ffe0ff803f8fb 0xefe00ffe0ff803f8

def z771 : W := mkw 0x62b7bde776d80006 0x8062b7bde776d800 0x000ffffffffc0008 0xf0000ffffffffc00

def z772 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe00ffe0ff801f8e3 0x6fe00ffe0ff801f8

def z773 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff0400238ff 0x8ffffffff0400238

def z774 : W := mkw 0x160ac3598da36600 0x24160ac3598da366 0x1e0fcfffbfe3c77f 0xff1e0fcfffbfe3c7

def z775 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x18083ff87f1e3f29 0xd318083ff87f1e3f

def z776 : W := mkw 0x1ff295e116fc4ba6 0x951ff295e116fc4b 0x1ff001f007fc0704 0x101ff001f007fc07

def z777 : W := mkw 0x82bb5b8aa86f6ba1 0x9a82bb5b8aa86f6b 0x07f9cf8bb8fc0727 0x5f07f9cf8bb8fc07

def z778 : W := mkw 0xe00d6a1ee903b401 0x0ae00d6a1ee903b4 0xe00ffe0fff03fffb 0xffe00ffe0fff03ff

def z779 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff6000fffffc0ff 0xfffff6000fffffc0

def z780 : W := mkw 0xa010000776d80002 0x0aa010000776d800 0xe7f0000ffffc00ff 0x7fe7f0000ffffc00

def z781 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xfff6318c47fffffc 0xf0fff6318c47ffff

def z782 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0xfff83ff87f1e3ffd 0xd3fff83ff87f1e3f

def z783 : W := mkw 0xc00d6a0888032000 0x0ac00d6a08880320 0xe00ffe0ff803f8fb 0xefe00ffe0ff803f8

def z784 : W := mkw 0x60b43084406cdba0 0x9060b43084406cdb 0xe7f0300440ffffdc 0x30e7f0300440ffff

def z785 : W := mkw 0xdfe7bde104800004 0x8fdfe7bde1048000 0xfffffff780e000f7 0xaffffffff780e000

def z786 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x180fc1ff87e3c72a 0xfc180fc1ff87e3c7

def z787 : W := mkw 0xdfe7bde012140984 0x8fdfe7bde0121409 0xfffffff87f1e3fff 0xdffffffff87f1e3f

def z788 : W := mkw 0xdfe7bde000204204 0x8fdfe7bde0002042 0xfffffff400e1c0f7 0xaffffffff400e1c0

def z789 : W := mkw 0xbd50846776d80006 0x0fbd50846776d800 0xfff0007ffffc00ff 0x7ffff0007ffffc00

def z790 : W := mkw 0x1f82d7e19eb56bc0 0x651f82d7e19eb56b 0x0787fe07f8fdf8c3 0x2f0787fe07f8fdf8

def z791 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff0000bfffc00a7 0x5ffff0000bfffc00

def z792 : W := mkw 0xdfe7bde00024dba4 0x9fdfe7bde00024db 0xfffffff400e3ffff 0xbffffffff400e3ff

def z793 : W := mkw 0xd667a94000000004 0x8ed667a940000000 0xfe7ffff0000000f7 0x8ffe7ffff0000000

def z794 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff0300ffffe38ff 0xfffff0300ffffe38

def z795 : W := mkw 0xb4d816bf6dce2dc2 0x4eb4d816bf6dce2d 0xe6783ff780e23f42 0xace6783ff780e23f

def z796 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e07c1ff87e3c74e 0x7c1e07c1ff87e3c7

def z797 : W := mkw 0x160ac3598da36600 0x24160ac3598da366 0x1e0fc1ffffe3ff7e 0xfc1e0fc1ffffe3ff

def z798 : W := mkw 0x22120104406cdba0 0x1022120104406cdb 0xe7f6018440ffffdc 0xb0e7f6018440ffff

def z799 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe60ffe0ff8e3f8ff 0xffe60ffe0ff8e3f8

def z800 : W := mkw 0xc00d6a0aa803b001 0x0ac00d6a0aa803b0 0x000ffe0fb803f87b 0xef000ffe0fb803f8

def z801 : W := mkw 0xe00d6a1ee903b401 0x0ae00d6a1ee903b4 0xe00ffffff803fffb 0xefe00ffffff803ff

def z802 : W := mkw 0xe01d6a0ee84bb001 0x0ae01d6a0ee84bb0 0xe67ffe0ff8e3f8fb 0xefe67ffe0ff8e3f8

def z803 : W := mkw 0x160ac3598da36600 0x24160ac3598da366 0x1e0fffff87e3ff7e 0xfc1e0fffff87e3ff

def z804 : W := mkw 0x098016b01b142dc0 0x41098016b01b142d 0x19883ff07f1c3fb5 0x9319883ff07f1c3f

def z805 : W := mkw 0x42b63180006cdba0 0x9042b63180006cdb 0xe7f6318000ffffd4 0x90e7f6318000ffff

def z806 : W := mkw 0x62b73984406cdba0 0x9062b73984406cdb 0xe7ffff8440ffffdc 0xb0e7ffff8440ffff

def z807 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x198ffff87f1e3fff 0xdf198ffff87f1e3f

def z808 : W := mkw 0xe03d6a0ee84bb021 0x9ae03d6a0ee84bb0 0xe07ffe0ff803f8fb 0xefe07ffe0ff803f8

def z809 : W := mkw 0x42affff889276fc4 0xe042affff889276f 0x000ffff00003ff00 0x80000ffff00003ff

def z810 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0fc1ff87e3c762 0xec1e0fc1ff87e3c7

def z811 : W := mkw 0xbd51884776d80006 0x0fbd51884776d800 0xfff1c00ffffc00ff 0x7ffff1c00ffffc00

def z812 : W := mkw 0x56a7bde000000004 0x8456a7bde0000000 0xfffffff0000000f6 0x8cfffffff0000000

def z813 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xffffc00ffffc00ff 0xffffffc00ffffc00

def z814 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6300440ffffc8 0x30e7f6300440ffff

def z815 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xffffcff000000067 0x0fffffcff0000000

def z816 : W := mkw 0xdf67ad6000000004 0x8fdf67ad60000000 0xfe7ffe70000000f3 0x8ffe7ffe70000000

def z817 : W := mkw 0xe9d53ea67a5cb9c3 0x4be9d53ea67a5cb9 0xe1f03e00781c3881 0x03e1f03e00781c38

def z818 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff801fffffc00ff 0xfffff801fffffc00

def z819 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff400e000ff 0xbffffffff400e000

def z820 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f0318440ffff8c 0x30e7f0318440ffff

def z821 : W := mkw 0xdfe7bde116900004 0x8fdfe7bde1169000 0xfffffffffffc00ff 0xfffffffffffffc00

def z822 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff0018ffffe07ff 0xfffff0018ffffe07

def z823 : W := mkw 0xe0056a06e801b001 0x0ae0056a06e801b0 0xe00ffe07f801f8f3 0xafe00ffe07f801f8

def z824 : W := mkw 0xa910000672580000 0x0ba9100006725800 0xfff0000ffffc00ff 0x7ffff0000ffffc00

def z825 : W := mkw 0xd6a7b9c000000000 0x8ed6a7b9c0000000 0xfffffff0000000f7 0x8ffffffff0000000

def z826 : W := mkw 0x42a6318000244b80 0x8042a6318000244b 0xe7f6318440ffffdc 0xb0e7f6318440ffff

def z827 : W := mkw 0xe9b53ea67a5cb9e1 0xdbe9b53ea67a5cb9 0xe1f03e00781c3881 0x03e1f03e00781c38

def z828 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfff9fff0000000a7 0x0ffff9fff0000000

def z829 : W := mkw 0x020a411881234600 0x00020a4118812346 0x1e0fc1ff87e3c77e 0xfc1e0fc1ff87e3c7

def z830 : W := mkw 0xcbe7bde000000004 0x8bcbe7bde0000000 0xf9fffff0000000b5 0x83f9fffff0000000

def z831 : W := mkw 0xbd50042776d80002 0x0fbd50042776d800 0xfff80e7ffffc00ff 0x7ffff80e7ffffc00

def z832 : W := mkw 0x1602814104a04200 0x041602814104a042 0x1e0fc1ff87e3c77e 0xfc1e0fc1ff87e3c7

def z833 : W := mkw 0x42affbd88927ffa1 0xb042affbd88927ff 0x000ffff00003ff00 0x80000ffff00003ff

def z834 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0x000ffe0ff803f82b 0xef000ffe0ff803f8

def z835 : W := mkw 0xc00d6a0aa803b001 0x0ac00d6a0aa803b0 0x000ffe0bf803f8bb 0xcf000ffe0bf803f8

def z836 : W := mkw 0x098854b893170dc0 0x41098854b893170d 0x198fc1ff871fc77e 0xfc198fc1ff871fc7

def z837 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7fff18440fffffe 0xbce7fff18440ffff

def z838 : W := mkw 0xf677a94764e8d226 0x9ef677a94764e8d2 0xe677c00780e1c042 0x2ce677c00780e1c0

def z839 : W := mkw 0x42af7fb88927ffe1 0xd042af7fb88927ff 0x000ffff00003ff00 0x80000ffff00003ff

def z840 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff8780000ff 0xcffffffff8780000

def z841 : W := mkw 0xdfe7bde116900006 0x8fdfe7bde1169000 0xfffffff0070000f7 0x8ffffffff0070000

def z842 : W := mkw 0x098016b01b142dc0 0x41098016b01b142d 0x19803ff07f1e3f9d 0x9319803ff07f1e3f

def z843 : W := mkw 0x1fd295f117fc4fc2 0x651fd295f117fc4f 0x1ff001f007fc0704 0x101ff001f007fc07

def z844 : W := mkw 0x1602c15185a14600 0x241602c15185a146 0x1e07c1f787e3c75e 0xbc1e07c1f787e3c7

def z845 : W := mkw 0x42a7bde000000004 0x8042a7bde0000000 0xe1fffff000000080 0x80e1fffff0000000

def z846 : W := mkw 0xdfe7bde000040984 0x8fdfe7bde0000409 0xfffffff0401c38f7 0x8ffffffff0401c38

def z847 : W := mkw 0x42a7bde000000004 0x8042a7bde0000000 0xe67ffff000000040 0x80e67ffff0000000

def z848 : W := mkw 0x9fe39de000000004 0x8f9fe39de0000000 0xfff9cff0000000f7 0x0ffff9cff0000000

def z849 : W := mkw 0xbd51080776d80002 0x0fbd51080776d800 0xfff9ce0ffffc00ff 0x7ffff9ce0ffffc00

def z850 : W := mkw 0xddc53ca000000000 0x0fddc53ca0000000 0xfffffff0000000f7 0x8ffffffff0000000

def z851 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x198e3ffc7f1ffffd 0xf3198e3ffc7f1fff

def z852 : W := mkw 0x9d49ca5bbf932403 0x2f9d49ca5bbf9324 0x1809ce7bbf000023 0x4f1809ce7bbf0000

def z853 : W := mkw 0xdfe7bde012100004 0x8fdfe7bde0121000 0xfffffff0781c00f7 0x8ffffffff0781c00

def z854 : W := mkw 0xc9e5bce000000004 0x8bc9e5bce0000000 0xe1f9fe7000000081 0x03e1f9fe70000000

def z855 : W := mkw 0xe9f53ca6725c99a6 0x9be9f53ca6725c99 0xe1f03e00781c3881 0x03e1f03e00781c38

def z856 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe007fe0ff803f8cb 0x6fe007fe0ff803f8

def z857 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6018440ffff4c 0x30e7f6018440ffff

def z858 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff40003c0ff 0xaffffffff40003c0

def z859 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xe7f0000ffffc00cb 0x7fe7f0000ffffc00

def z860 : W := mkw 0x2910000776d80002 0x012910000776d800 0xfff0000ffffc00fd 0x73fff0000ffffc00

def z861 : W := mkw 0xb450000776d80002 0x0eb450000776d800 0xe7f0000ffffc00de 0x7ce7f0000ffffc00

def z862 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe00ffe0fb803f863 0xefe00ffe0fb803f8

def z863 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xf9fffff0000000a3 0x8ff9fffff0000000

def z864 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe00fff8ff803ffff 0xffe00fff8ff803ff

def z865 : W := mkw 0x1fe295f117b44fc4 0xe51fe295f117b44f 0x1ff001f007fc0704 0x101ff001f007fc07

def z866 : W := mkw 0x098014a012140980 0x01098014a0121409 0x19883ff87f1e3fbd 0xd319883ff87f1e3f

def z867 : W := mkw 0xdfe7bde00020d224 0x9fdfe7bde00020d2 0xfffffff00001c0f7 0x8ffffffff00001c0

def z868 : W := mkw 0x09e816b81b162dc4 0xc109e816b81b162d 0x19f83ff87f1e3fbd 0xd319f83ff87f1e3f

def z869 : W := mkw 0x2018421ddfffffe0 0x702018421ddfffff 0x0000000fffffff08 0x700000000fffffff

def z870 : W := mkw 0x80094a0aa8032001 0x0a80094a0aa80320 0x000ffe0ff803f8fb 0xef000ffe0ff803f8

def z871 : W := mkw 0x166ac15985a34604 0xa4166ac15985a346 0x1e7fc1ff87e3c77e 0xfc1e7fc1ff87e3c7

def z872 : W := mkw 0xdfe7bde104800004 0x8fdfe7bde1048000 0xfffffff007e000f7 0x9ffffffff007e000

def z873 : W := mkw 0x098856b89b172dc0 0x41098856b89b172d 0x19883fffff1fffbd 0xf319883fffff1fff

def z874 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe18ffe0ff81ff8ff 0xffe18ffe0ff81ff8

def z875 : W := mkw 0x1602c15185a14600 0x241602c15185a146 0x1e0fc1f787e1c776 0xbc1e0fc1f787e1c7

def z876 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe7fffe0ff803f8ff 0xefe7fffe0ff803f8

def z877 : W := mkw 0x9d418c6000000004 0x0f9d418c60000000 0xf9f9ce70000000a3 0x0ff9f9ce70000000

def z878 : W := mkw 0x9d418c6000000004 0x0f9d418c60000000 0xfe79ce7000000063 0x0ffe79ce70000000

def z879 : W := mkw 0xdf67ad6000000004 0x8fdf67ad60000000 0xffffce70000000f7 0x0fffffce70000000

def z880 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0fc1ffffe3c7ff 0xff1e0fc1ffffe3c7

def z881 : W := mkw 0xbd510c2776d80006 0x0fbd510c2776d800 0xfff00e0ffffc00ff 0x7ffff00e0ffffc00

def z882 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6318040ffff84 0x90e7f6318040ffff

def z883 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0fffff87e3c7ff 0xff1e0fffff87e3c7

def z884 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xffffffff800000ff 0xefffffffff800000

def z885 : W := mkw 0x000802181b162dc0 0x40000802181b162d 0x18083ff87f1e3fbd 0xd318083ff87f1e3f

def z886 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff0000ffffc004e 0x7cfff0000ffffc00

def z887 : W := mkw 0xf657e947e4e9d203 0x2ef657e947e4e9d2 0xe677c00780e1c042 0x2ce677c00780e1c0

def z888 : W := mkw 0x1fb295f117fc4fe0 0xf51fb295f117fc4f 0x1ff001f007fc0704 0x101ff001f007fc07

def z889 : W := mkw 0x0088129809062d80 0x000088129809062d 0x19883ff87f1e3fbd 0xd319883ff87f1e3f

def z890 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6318fc0fffffe 0xfce7f6318fc0ffff

def z891 : W := mkw 0xdfe7bde104a04204 0xafdfe7bde104a042 0xfffffff000e000f7 0x8ffffffff000e000

def z892 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0xffffc1ff87e3c7fe 0xfcffffc1ff87e3c7

def z893 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff0000ffffc00e3 0x6ffff0000ffffc00

def z894 : W := mkw 0xe0056a06e801b001 0x0ae0056a06e801b0 0xe007fe07f803f8db 0xafe007fe07f803f8

def z895 : W := mkw 0xdfe7bde000040984 0x8fdfe7bde0000409 0xfffffff0001c07f7 0x9ffffffff0001c07

def z896 : W := mkw 0xdfe7bde000244ba4 0x9fdfe7bde000244b 0xfffffff0000007f7 0x8ffffffff0000007

def z897 : W := mkw 0xe00d6a1ee903b401 0x0ae00d6a1ee903b4 0xf80ffe7fff03f8fb 0xeff80ffe7fff03f8

def z898 : W := mkw 0x62b635a4406cdba0 0x9062b635a4406cdb 0xe7fe3ff440ffffdc 0xb0e7fe3ff440ffff

def z899 : W := mkw 0x22921184406c4b80 0x0022921184406c4b 0xe7f6318440ffffdc 0xb0e7f6318440ffff

def z900 : W := mkw 0xdfe7bde012100004 0x8fdfe7bde0121000 0xfffffff83f0000f7 0xcffffffff83f0000

def z901 : W := mkw 0x160a83590da26600 0x24160a83590da266 0x1e083ff87fe23fbd 0xd31e083ff87fe23f

def z902 : W := mkw 0xf637e947e4e9d221 0xbef637e947e4e9d2 0xe677c00780e1c042 0x2ce677c00780e1c0

def z903 : W := mkw 0x3410000776d80002 0x043410000776d800 0xfff0000ffffc00fe 0x7cfff0000ffffc00

def z904 : W := mkw 0xc2e7bde000000004 0x8ac2e7bde0000000 0xe07ffff000000000 0x80e07ffff0000000

def z905 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff000000085 0x83fffffff0000000

def z906 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff000000046 0x8cfffffff0000000

def z907 : W := mkw 0x62362104406cdba0 0x9062362104406cdb 0xe7f6000440ffffdc 0x30e7f6000440ffff

def z908 : W := mkw 0x621621044068d200 0x00621621044068d2 0xe7f6318440ffffdc 0xb0e7f6318440ffff

def z909 : W := mkw 0x090802181b122400 0x01090802181b1224 0x19883ff87f1e3fbd 0xd319883ff87f1e3f

def z910 : W := mkw 0x5fe7bde000000004 0x855fe7bde0000000 0xfffffff0000000d4 0x80fffffff0000000

def z911 : W := mkw 0x22b21184406cdba0 0x9022b21184406cdb 0xe7f0018440ffffdc 0x30e7f0018440ffff

def z912 : W := mkw 0x5fa6b5e000000000 0x855fa6b5e0000000 0xfffffff0000000f7 0x8ffffffff0000000

def z913 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x19883ff87f1c3fa5 0x5319883ff87f1c3f

def z914 : W := mkw 0xcbe7bde000000004 0x8bcbe7bde0000000 0xe1fffff0000000f3 0x8fe1fffff0000000

def z915 : W := mkw 0xb410000764c80000 0x0eb410000764c800 0xfff0000ffffc00ff 0x7ffff0000ffffc00

def z916 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x19883ff87f1e3fa1 0xc319883ff87f1e3f

def z917 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6318c78fffffd 0xf3e7f6318c78ffff

def z918 : W := mkw 0xdfe7bde000204204 0x8fdfe7bde0002042 0xfffffff00003c7f7 0x8ffffffff00003c7

def z919 : W := mkw 0xe01d6a0ee84bb001 0x0ae01d6a0ee84bb0 0xe00ffe0ff8fff8fb 0xffe00ffe0ff8fff8

def z920 : W := mkw 0xe05d6a0ee84bb003 0x0ae05d6a0ee84bb0 0xe07ffe0ff803f8fb 0xefe07ffe0ff803f8

def z921 : W := mkw 0xdfe7bde232100006 0x8fdfe7bde2321000 0xfffffff0380000f7 0x8ffffffff0380000

def z922 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x1f883ffc7ffe3ffd 0xf31f883ffc7ffe3f

def z923 : W := mkw 0xdfe7bde104800004 0x8fdfe7bde1048000 0xfffffffb870000f7 0xcffffffffb870000

def z924 : W := mkw 0x1602c15185a14600 0x241602c15185a146 0x1e07c1ff87e1c77e 0x7c1e07c1ff87e1c7

def z925 : W := mkw 0xdde5bce000000004 0x8fdde5bce0000000 0xfff9fe70000000f7 0x0ffff9fe70000000

def z926 : W := mkw 0x60142004406cdba0 0x1060142004406cdb 0xe7f6300440ffffdc 0xb0e7f6300440ffff

def z927 : W := mkw 0xc00d6a0aa803b001 0x0ac00d6a0aa803b0 0xe00ffe0bb803f8f3 0xcfe00ffe0bb803f8

def z928 : W := mkw 0x20901084406cdba0 0x1020901084406cdb 0xe7f0318440ffffdc 0xb0e7f0318440ffff

def z929 : W := mkw 0x9d50000336d80002 0x0f9d50000336d800 0xfff0000bbffc00f7 0x5ffff0000bbffc00

def z930 : W := mkw 0x9fc295e000000000 0x0f9fc295e0000000 0xfffffff0000000f7 0x8ffffffff0000000

def z931 : W := mkw 0xdfe7bde000244b84 0x8fdfe7bde000244b 0xfffffff440ffffff 0xbffffffff440ffff

def z932 : W := mkw 0x2018421fffdfbdc3 0x402018421fffdfbd 0x0000000fffffff08 0x700000000fffffff

def z933 : W := mkw 0xd6e7bde000000004 0x8ed6e7bde0000000 0xe67ffff0000000f3 0x8fe67ffff0000000

def z934 : W := mkw 0xd667ad6000000004 0x8ed667ad60000000 0xe67fce7000000042 0x0ce67fce70000000

def z935 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff0000207ff 0x9ffffffff0000207

def z936 : W := mkw 0x62b63184406cdba0 0x9062b63184406cdb 0xe7f6318400ffff44 0xb0e7f6318400ffff

def z937 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x19803ff87f1e3f8d 0x5319803ff87f1e3f

def z938 : W := mkw 0xbd50000776d89002 0x0fbd50000776d890 0xfff0000ffffff8ff 0x7ffff0000ffffff8

def z939 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xf80ffe0fff03f8ff 0xfff80ffe0fff03f8

def z940 : W := mkw 0xdfe7bde0000499a4 0x9fdfe7bde0000499 0xfffffff0000038f7 0x8ffffffff0000038

def z941 : W := mkw 0x160ac15985a34600 0x24160ac15985a346 0x1e0fc1ff87e1c766 0x7c1e0fc1ff87e1c7

def z942 : W := mkw 0xcbe7bde000000004 0x8bcbe7bde0000000 0xe7fffff0000000d5 0x83e7fffff0000000

def z943 : W := mkw 0x098856b89b172dc0 0x41098856b89b172d 0x1989fffbff1e3fbf 0xdf1989fffbff1e3f

def z944 : W := mkw 0xdfe7bde000000004 0x8fdfe7bde0000000 0xfffffff8070000ff 0xdffffffff8070000

def z945 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe00ffe07f803f8c3 0xafe00ffe07f803f8

def z946 : W := mkw 0xdfe7bde324800006 0x8fdfe7bde3248000 0xfffffff3800000f7 0x8ffffffff3800000

def z947 : W := mkw 0x3d10000556d80000 0x053d10000556d800 0xfff0000ffffc00ff 0x7ffff0000ffffc00

def z948 : W := mkw 0xbd50000776d80002 0x0fbd50000776d800 0xfff83e0ffffc00ff 0xfffff83e0ffffc00

def z949 : W := mkw 0x2018421fedefffa1 0x302018421fedefff 0x0000000fffffff08 0x700000000fffffff

def z950 : W := mkw 0x9f438d6000000004 0x0f9f438d60000000 0xffffcff0000000f7 0x8fffffcff0000000

def z951 : W := mkw 0x098816b81b162dc0 0x41098816b81b162d 0x19883fffff1e3fff 0xff19883fffff1e3f

def z952 : W := mkw 0x2018421ffffbf603 0x202018421ffffbf6 0x0000000fffffff08 0x700000000fffffff

def z953 : W := mkw 0x098856b89b172dc0 0x41098856b89b172d 0x198ffff87f1fffbd 0xd3198ffff87f1fff

def z954 : W := mkw 0x1408401985830400 0x0414084019858304 0x1e0fc1ff87e3c77e 0xfc1e0fc1ff87e3c7

def z955 : W := mkw 0xdde5bce000000004 0x8fdde5bce0000000 0xf9fffe70000000f3 0x8ff9fffe70000000

def z956 : W := mkw 0xd6e7bde000000004 0x8ed6e7bde0000000 0xe7fffff0000000d6 0x8ce7fffff0000000

def z957 : W := mkw 0xe0056a06e801b001 0x0ae0056a06e801b0 0xe007fe0ff801f8fb 0x6fe007fe0ff801f8

def z958 : W := mkw 0xdfe7bde012100004 0x8fdfe7bde0121000 0xfffffff0071c00f7 0x9ffffffff0071c00

def z959 : W := mkw 0x600c620cc803b000 0x00600c620cc803b0 0xe00ffe0ff803f8fb 0xefe00ffe0ff803f8

def z960 : W := mkw 0x2018421fffff6fc2 0x602018421fffff6f 0x0000000fffffff08 0x700000000fffffff

def z961 : W := mkw 0x9d49ce799f932444 0x6f9d49ce799f9324 0x1809ce7bbf000023 0x4f1809ce7bbf0000

def z962 : W := mkw 0xdd45ac6000000004 0x0fdd45ac60000000 0xfffffe70000000f7 0x8ffffffe70000000

def z963 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xf80ffffff803f8ff 0xeff80ffffff803f8

def z964 : W := mkw 0xa008420ee8032000 0x0aa008420ee80320 0xe00ffe0ff803f8fb 0xefe00ffe0ff803f8

def z965 : W := mkw 0xe00d6a0ee803b001 0x0ae00d6a0ee803b0 0xe00ffe0bf803f8a3 0xcfe00ffe0bf803f8

def z966 : W := mkw 0x2018421efb7fffe1 0x502018421efb7fff 0x0000000fffffff08 0x700000000fffffff

def z967 : W := mkw 0x62b63186606cdba0 0x9062b63186606cdb 0xe7f6318ff8ffffdc 0xf0e7f6318ff8ffff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z2,z4,z5,z6]),(0,[z8,z0,z1,z2,z4,z5,z6])],[(0,[z9,z0,z1,z2,z4,z5,z10]),(0,[z0,z1,z2,z4,z5,z11,z6]),(0,[z12,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z13,z5,z6]),(0,[z0,z1,z2,z4,z14,z5,z6])],[(0,[z0,z15,z1,z2,z4,z5,z6]),(0,[z0,z2,z16,z4,z17,z5,z6]),(0,[z0,z1,z2,z18,z4,z5,z6]),(0,[z0,z1,z2,z19,z4,z5,z6])],[],[(0,[z0,z1,z2,z4,z5,z6,z20]),(0,[z21,z1,z2,z22,z4,z5,z6])],[(0,[z0,z1,z2,z23,z4,z5,z6])],[(0,[z24,z0,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z2,z4,z5,z6]),(0,[z0,z26,z1,z2,z4,z27,z6]),(0,[z0,z1,z2,z4,z28,z5,z6]),(0,[z0,z1,z2,z29,z4,z5,z6]),(0,[z0,z1,z30,z2,z31,z4,z5])],[(0,[z0,z1,z2,z4,z32,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z33]),(0,[z0,z34,z1,z2,z4,z5,z6]),(0,[z35,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z36,z4,z5,z6]),(0,[z0,z1,z37,z2,z5,z6,z38])]],
   [[(0,[z0,z1,z39,z2,z4,z5,z6]),(0,[z0,z1,z2,z40,z4,z5,z6]),(0,[z0,z1,z2,z4,z41,z5,z6])],[(0,[z0,z1,z2,z4,z5,z42,z6]),(0,[z0,z1,z2,z4,z43,z6,z44]),(0,[z0,z1,z2,z4,z5,z6,z45])],[(0,[z0,z1,z2,z4,z5,z6,z46]),(0,[z0,z1,z47,z2,z4,z5,z6]),(0,[z0,z1,z2,z48,z4,z6,z49]),(0,[z0,z1,z50,z2,z4,z5,z6]),(0,[z0,z1,z51,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z52]),(0,[z0,z1,z37,z2,z4,z53,z6])],[(0,[z9,z0,z1,z2,z4,z5,z6]),(0,[z54,z0,z2,z16,z4,z5,z6]),(0,[z0,z1,z55,z2,z4,z56,z6]),(0,[z0,z1,z2,z57,z4,z5,z6])],[(0,[z0,z1,z58,z2,z4,z5,z6]),(1,[z59,z1,z2,z4,z60,z6])],[(0,[z0,z61,z2,z4,z5,z6,z62]),(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z64,z1,z2,z4,z65,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z66]),(0,[z0,z1,z2,z4,z5,z67,z6]),(0,[z0,z1,z2,z4,z5,z6,z68]),(0,[z0,z1,z2,z4,z5,z6,z38]),(0,[z0,z1,z69,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z27,z5,z6]),(0,[z0,z1,z70,z2,z71,z4,z6])]],
   [[(0,[z72,z0,z1,z2,z4,z5,z6]),(0,[z73,z74,z1,z2,z4,z5,z6])],[(0,[z0,z75,z1,z2,z4,z5,z6]),(0,[z0,z1,z76,z2,z71,z4,z6])],[(0,[z0,z1,z77,z4,z5,z6,z49]),(0,[z0,z1,z2,z78,z4,z5,z6]),(0,[z0,z1,z2,z79,z4,z5,z6]),(0,[z80,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z81,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z82,z83]),(0,[z0,z1,z84,z4,z5,z6,z85])],[(0,[z86,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z87,z2,z4,z5,z6]),(0,[z88,z0,z1,z89,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z56,z6]),(0,[z90,z0,z1,z2,z4,z5,z6])],[(0,[z91,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z30,z2,z4,z5,z6])],[(0,[z92,z1,z2,z4,z5,z6,z93]),(0,[z0,z1,z2,z4,z5,z60,z6]),(0,[z0,z1,z2,z4,z94,z5,z6])],[(0,[z95,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z96,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z55,z2,z5,z6,z38]),(0,[z97,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z98,z2,z4,z5,z6]),(0,[z99,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z100,z61,z2,z4,z5]),(0,[z0,z1,z101,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z102]),(0,[z0,z1,z2,z4,z5,z6,z103])],[(1,[z0,z1,z100,z2,z4,z5]),(1,[z0,z1,z2,z4,z104,z6]),(0,[z0,z1,z105,z2,z4,z5,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z106,z4,z5,z6]),(0,[z107,z0,z1,z2,z4,z5,z62]),(0,[z0,z1,z108,z2,z4,z5,z6]),(0,[z0,z1,z2,z31,z5,z6,z109])],[(0,[z0,z1,z2,z4,z5,z6,z110]),(0,[z0,z1,z111,z2,z4,z5,z6])],[(0,[z0,z1,z2,z71,z4,z60,z6]),(0,[z112,z0,z1,z2,z4,z5,z6]),(0,[z95,z0,z113,z2,z4,z5,z6]),(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z115,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z116,z5,z6]),(0,[z0,z1,z117,z2,z4,z6,z44])],[(1,[z0,z1,z2,z4,z5,z10]),(0,[z0,z1,z2,z118,z4,z5,z6]),(0,[z0,z1,z2,z119,z4,z5,z6]),(0,[z0,z1,z2,z120,z4,z5,z6]),(0,[z0,z1,z121,z2,z4,z5,z6]),(0,[z0,z122,z1,z2,z4,z5,z6]),(0,[z0,z1,z123,z2,z4,z5,z6]),(1,[z0,z1,z124,z30,z2,z5])]],
   [[(0,[z125,z0,z1,z2,z4,z126,z6]),(1,[z0,z1,z2,z4,z127,z6]),(0,[z0,z1,z2,z128,z4,z5,z6])],[(0,[z0,z129,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z130,z4,z5,z6]),(0,[z0,z1,z131,z2,z4,z5,z6])],[(0,[z0,z1,z132,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z133,z6]),(0,[z0,z1,z2,z4,z5,z6,z134]),(0,[z0,z1,z2,z135,z4,z5,z6]),(0,[z107,z136,z1,z2,z4,z5,z6]),(1,[z0,z137,z2,z4,z5,z82]),(0,[z0,z1,z30,z2,z4,z5,z85])],[(0,[z0,z1,z138,z2,z4,z5,z6]),(0,[z0,z1,z139,z2,z4,z5,z6]),(0,[z0,z1,z140,z2,z4,z5,z6]),(0,[z0,z1,z2,z141,z4,z5,z6]),(0,[z0,z1,z2,z142,z4,z5,z6]),(0,[z143,z0,z1,z2,z4,z5,z6])],[(0,[z1,z61,z2,z4,z5,z6,z93]),(0,[z144,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z145])],[(0,[z64,z0,z1,z2,z4,z5,z6]),(0,[z73,z0,z137,z1,z2,z4,z5]),(1,[z146,z0,z1,z147,z4,z5]),(0,[z0,z1,z2,z148,z4,z5,z6])],[(0,[z149,z0,z1,z61,z2,z4,z5]),(0,[z73,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z147,z4,z5,z6])],[(0,[z0,z1,z2,z150,z4,z5,z6]),(0,[z0,z113,z1,z2,z4,z53,z6]),(1,[z0,z1,z2,z151,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z152])]],
   [[(0,[z0,z1,z2,z153,z4,z5,z6]),(0,[z0,z1,z2,z154,z4,z5,z6]),(0,[z0,z1,z155,z2,z4,z5,z6]),(0,[z0,z1,z156,z117,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z6,z62])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z157,z0,z1,z2,z4,z5,z6]),(0,[z0,z158,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z77,z4,z42,z6]),(0,[z0,z1,z159,z2,z4,z5,z6]),(0,[z0,z1,z2,z160,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z161,z6])],[(0,[z9,z0,z61,z2,z4,z5,z6]),(0,[z162,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z163,z2,z4,z5,z6]),(0,[z0,z1,z2,z164,z4,z5,z6]),(0,[z165,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z126,z6]),(0,[z0,z1,z2,z166,z4,z5,z6]),(0,[z0,z1,z167,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z6,z49]),(0,[z0,z1,z2,z71,z4,z53,z6]),(0,[z0,z1,z2,z4,z5,z6,z168])],[],[],[(0,[z0,z1,z169,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z170]),(0,[z95,z0,z2,z4,z171,z5,z6]),(0,[z0,z1,z172,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z173]),(0,[z0,z1,z124,z2,z4,z5,z6]),(0,[z0,z1,z30,z2,z5,z6,z109])]],
   [[(0,[z0,z1,z2,z4,z5,z82,z93]),(0,[z0,z1,z2,z31,z4,z5,z109])],[(0,[z0,z1,z2,z4,z65,z5,z6]),(0,[z0,z1,z2,z4,z174,z5,z6])],[(0,[z175,z0,z1,z2,z4,z5,z6]),(0,[z64,z0,z1,z2,z4,z65,z6]),(0,[z0,z1,z2,z4,z5,z6,z176])],[(0,[z1,z89,z2,z177,z4,z5,z6]),(0,[z0,z178,z2,z179,z4,z5,z6]),(0,[z180,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z181]),(0,[z0,z1,z2,z182,z4,z5,z6]),(0,[z0,z1,z2,z183,z4,z5,z6]),(0,[z0,z1,z2,z4,z171,z5,z6]),(1,[z95,z0,z2,z4,z171,z6]),(0,[z0,z1,z184,z2,z4,z5,z6])],[(1,[z0,z185,z2,z4,z5,z6]),(0,[z0,z1,z186,z2,z4,z5,z6]),(0,[z0,z1,z187,z2,z4,z5,z6])],[(0,[z188,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z189]),(0,[z0,z1,z2,z190,z4,z5,z6]),(0,[z0,z191,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z192,z4,z5,z6])],[(1,[z88,z1,z89,z4,z5,z6]),(0,[z0,z1,z2,z193,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z194]),(0,[z0,z1,z2,z4,z5,z195,z6]),(0,[z0,z1,z196,z2,z4,z5,z6])]],
   [[(0,[z0,z137,z197,z2,z4,z5,z6]),(0,[z0,z1,z198,z2,z4,z5,z6]),(0,[z0,z1,z199,z2,z4,z5,z6])],[(0,[z0,z1,z200,z2,z4,z5,z6]),(0,[z0,z1,z201,z2,z4,z5,z6]),(0,[z0,z1,z2,z202,z4,z5,z6]),(0,[z0,z1,z203,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z204])],[(0,[z0,z1,z2,z4,z205,z5,z6]),(0,[z0,z1,z2,z4,z206,z5,z6]),(0,[z207,z0,z1,z2,z4,z208,z6]),(0,[z0,z1,z70,z71,z4,z5,z6])],[(0,[z0,z1,z209,z2,z4,z5,z6]),(0,[z0,z1,z210,z2,z4,z5,z6]),(0,[z0,z1,z172,z4,z5,z6,z211]),(0,[z0,z1,z2,z4,z212,z5,z6])],[(0,[z92,z0,z197,z2,z4,z5,z6]),(0,[z213,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z214,z4,z5,z6]),(0,[z0,z1,z215,z2,z4,z5,z6])],[(0,[z0,z26,z2,z4,z17,z5,z6]),(1,[z0,z1,z55,z77,z5,z6]),(0,[z0,z216,z1,z2,z4,z5,z6])],[(0,[z125,z0,z1,z177,z4,z5,z6]),(0,[z0,z1,z217,z2,z4,z5,z6]),(0,[z0,z1,z218,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z219]),(0,[z0,z1,z2,z220,z4,z5,z6]),(0,[z207,z0,z2,z179,z4,z5,z6])]],
   [[(0,[z221,z0,z1,z2,z4,z5,z6]),(0,[z222,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z223,z2,z4,z5,z6]),(0,[z0,z224,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z225,z6]),(0,[z226,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z227,z4,z5,z6])],[(0,[z9,z1,z61,z2,z4,z5,z6]),(0,[z0,z1,z2,z228,z4,z5,z6]),(0,[z59,z1,z2,z4,z5,z60,z6]),(0,[z229,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z230])],[(0,[z0,z1,z2,z4,z231,z5,z6]),(0,[z0,z1,z2,z4,z5,z232,z6]),(0,[z0,z1,z2,z4,z5,z6,z233])],[(0,[z234,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z235]),(0,[z0,z1,z2,z236,z4,z5,z6])],[(0,[z0,z1,z2,z237,z4,z5,z6])],[(0,[z0,z137,z1,z2,z4,z5,z6]),(0,[z0,z1,z238,z2,z4,z5,z6])],[(0,[z239,z0,z1,z2,z4,z5,z6]),(0,[z125,z1,z2,z177,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z240]),(0,[z0,z1,z55,z77,z4,z5,z6]),(0,[z0,z1,z241,z2,z77,z4,z6])]],
   [[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z242,z5,z6]),(0,[z0,z1,z243,z2,z4,z5,z6]),(0,[z244,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z48,z4,z5,z6])],[(0,[z0,z1,z2,z245,z4,z5,z6]),(0,[z0,z1,z246,z2,z4,z5,z6])],[(0,[z92,z0,z1,z2,z4,z5,z6]),(0,[z95,z0,z1,z2,z4,z171,z6]),(0,[z0,z1,z70,z140,z4,z5,z6])],[(0,[z0,z247,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z248,z6]),(0,[z0,z1,z2,z4,z5,z249,z6])],[(0,[z0,z1,z250,z2,z4,z5,z6]),(0,[z0,z251,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z252]),(0,[z0,z1,z2,z4,z5,z6,z253]),(0,[z0,z1,z2,z254,z4,z5,z6]),(0,[z0,z1,z255,z2,z4,z5,z6])],[(0,[z64,z59,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z256,z5,z6]),(0,[z207,z0,z1,z179,z4,z5,z6]),(0,[z0,z1,z2,z257,z4,z5,z6]),(0,[z0,z137,z1,z2,z4,z5,z82])],[(0,[z0,z1,z258,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z259])],[(0,[z0,z1,z2,z260,z4,z5,z6]),(0,[z261,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z262,z2,z4,z5,z6]),(0,[z0,z1,z70,z37,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z263]),(0,[z0,z1,z140,z2,z4,z6,z38])],[(0,[z264,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z265,z4,z5,z6]),(0,[z266,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z76,z37,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z267,z6]),(1,[z0,z1,z76,z37,z2,z6])],[(0,[z0,z268,z1,z2,z4,z5,z6]),(0,[z0,z1,z269,z2,z4,z5,z6]),(0,[z0,z1,z70,z77,z4,z5,z6]),(1,[z0,z1,z70,z71,z4,z6])],[(0,[z0,z1,z156,z117,z2,z4,z6])],[(0,[z0,z1,z270,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z271,z5,z6]),(0,[z0,z1,z2,z272,z4,z5,z6]),(0,[z273,z0,z1,z2,z4,z5,z6])],[(0,[z274,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z171,z5,z53,z6]),(0,[z0,z1,z2,z275,z4,z5,z6]),(0,[z0,z1,z37,z2,z48,z4,z6]),(0,[z0,z1,z2,z276,z4,z5,z6])],[(0,[z277,z0,z1,z2,z4,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z278]),(0,[z279,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z280,z4,z5,z6]),(0,[z0,z1,z281,z2,z4,z5,z6])]],
   [[(0,[z282,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z283,z2,z4,z5,z6]),(0,[z0,z1,z284,z2,z4,z5,z6])],[(0,[z64,z0,z1,z2,z4,z60,z6]),(0,[z0,z1,z2,z285,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z83,z62]),(0,[z0,z1,z2,z4,z5,z6,z286]),(0,[z0,z1,z287,z2,z4,z5,z6])],[(0,[z21,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z288,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z289,z5,z6]),(0,[z0,z1,z2,z4,z290,z5,z6]),(0,[z107,z0,z137,z2,z4,z5,z6]),(0,[z0,z1,z291,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z292,z5,z6]),(0,[z0,z1,z293,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z294,z5,z6])],[(0,[z295,z0,z1,z2,z4,z5,z6]),(0,[z0,z296,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z297]),(0,[z0,z1,z2,z298,z4,z5,z6]),(0,[z0,z1,z299,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z211]),(0,[z0,z1,z2,z4,z5,z6,z300]),(0,[z0,z1,z2,z4,z301,z5,z6]),(0,[z0,z1,z124,z2,z4,z5,z109])],[(0,[z0,z1,z2,z4,z65,z6,z38]),(0,[z54,z0,z1,z2,z17,z5,z6])],[(0,[z0,z1,z2,z4,z302,z5,z6]),(0,[z303,z0,z1,z2,z4,z5,z6]),(0,[z304,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z305,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z306,z4,z5,z6]),(0,[z146,z0,z1,z2,z147,z4,z5])],[(0,[z0,z1,z2,z4,z171,z6,z38])],[(0,[z21,z0,z1,z2,z4,z5,z6]),(0,[z73,z0,z1,z2,z4,z5,z83]),(0,[z0,z307,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z308,z5,z6]),(0,[z0,z1,z309,z2,z4,z5,z6]),(0,[z0,z1,z172,z55,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z310])],[(0,[z0,z1,z2,z311,z4,z5,z6]),(0,[z0,z1,z2,z4,z312,z5,z6]),(0,[z0,z1,z2,z4,z5,z313,z6]),(0,[z0,z1,z2,z4,z5,z314,z6])],[(0,[z0,z1,z2,z315,z4,z5,z6]),(0,[z0,z1,z55,z2,z316,z4,z6]),(0,[z0,z1,z70,z2,z4,z6,z49])],[(0,[z0,z137,z61,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z317,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z318])],[(0,[z0,z319,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z320]),(0,[z0,z1,z76,z2,z4,z6,z49]),(0,[z0,z1,z321,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z322,z5,z6]),(0,[z0,z1,z2,z4,z5,z53,z6]),(0,[z0,z1,z55,z2,z5,z6,z211])]],
   [[(0,[z0,z1,z2,z4,z323,z5,z6]),(0,[z125,z0,z1,z89,z4,z5,z6]),(0,[z324,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z325,z2,z4,z5,z6]),(0,[z0,z1,z2,z326,z4,z5,z6])],[(0,[z0,z1,z327,z2,z4,z5,z6]),(0,[z0,z1,z328,z2,z4,z5,z6])],[(0,[z0,z1,z2,z329,z4,z5,z6]),(0,[z0,z1,z330,z2,z4,z5,z6]),(0,[z0,z331,z1,z2,z4,z5,z6])],[(1,[z21,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z179,z4,z5,z6]),(0,[z0,z1,z332,z2,z4,z5,z6]),(0,[z0,z1,z333,z2,z4,z5,z6]),(0,[z54,z0,z1,z2,z16,z5,z6]),(0,[z107,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z334,z2,z4,z5,z6])],[(0,[z0,z1,z335,z2,z4,z5,z6]),(0,[z0,z1,z336,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z10]),(0,[z0,z337,z1,z2,z4,z5,z6]),(0,[z0,z268,z1,z179,z4,z5,z6]),(0,[z0,z1,z2,z338,z4,z5,z6]),(0,[z0,z1,z147,z4,z5,z6,z85])],[(0,[z339,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z172,z2,z5,z6,z38]),(0,[z0,z1,z2,z340,z4,z5,z6])],[(0,[z341,z0,z1,z2,z32,z5,z6]),(0,[z0,z342,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z343,z4,z5,z6]),(0,[z344,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z345,z6]),(1,[z73,z1,z2,z4,z5,z93]),(1,[z0,z1,z346,z2,z5,z6]),(0,[z347,z0,z1,z2,z4,z5,z6]),(0,[z0,z348,z1,z2,z4,z5,z6]),(0,[z0,z1,z349,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z350,z5,z6]),(0,[z0,z1,z2,z4,z351,z5,z6])],[(0,[z74,z0,z137,z1,z2,z4,z5]),(0,[z0,z1,z352,z2,z4,z5,z6]),(0,[z107,z0,z1,z2,z4,z5,z82]),(0,[z0,z1,z2,z4,z5,z6,z353]),(1,[z0,z1,z276,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z5,z44])],[(0,[z0,z1,z2,z4,z354,z5,z6]),(0,[z355,z0,z1,z2,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z84,z2,z147,z4,z5])],[(0,[z59,z0,z1,z2,z4,z5,z6]),(0,[z356,z0,z1,z2,z4,z5,z6]),(0,[z73,z0,z357,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z208,z6]),(1,[z0,z113,z2,z4,z53,z6])],[(0,[z0,z1,z2,z358,z4,z5,z6]),(1,[z0,z1,z2,z4,z126,z6]),(0,[z359,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z60,z6,z49]),(0,[z0,z1,z37,z2,z4,z171,z6]),(1,[z0,z1,z2,z4,z360,z5]),(0,[z0,z1,z140,z4,z5,z6,z49]),(0,[z0,z1,z2,z48,z4,z6,z38]),(0,[z0,z1,z2,z4,z361,z5,z6])],[(0,[z0,z1,z2,z4,z5,z362,z6]),(0,[z0,z1,z55,z2,z77,z5,z6]),(0,[z0,z1,z2,z4,z363,z5,z6]),(0,[z0,z1,z364,z2,z4,z5,z6]),(0,[z0,z1,z365,z2,z4,z5,z6])],[(0,[z0,z1,z2,z177,z4,z5,z6]),(1,[z341,z1,z2,z32,z5,z6]),(0,[z0,z1,z366,z2,z4,z5,z6]),(0,[z0,z1,z2,z367,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z368,z4,z5,z6]),(1,[z0,z357,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z369,z0,z1,z2,z4,z5,z6]),(0,[z107,z0,z2,z4,z5,z6,z62]),(1,[z0,z1,z2,z48,z6,z38])],[],[(0,[z0,z1,z2,z4,z370,z5,z6]),(0,[z0,z1,z2,z4,z371,z5,z6]),(0,[z0,z1,z172,z2,z4,z360,z5])],[(0,[z0,z372,z1,z2,z4,z5,z6]),(0,[z373,z0,z1,z2,z4,z5,z6]),(1,[z0,z26,z2,z17,z5,z6]),(0,[z374,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z375,z2,z4,z5,z6]),(0,[z0,z1,z376,z2,z4,z5,z6]),(0,[z0,z1,z124,z30,z2,z4,z5])],[(0,[z0,z1,z377,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z378,z6]),(0,[z0,z1,z379,z2,z4,z5,z6]),(0,[z0,z380,z1,z2,z4,z5,z6])],[(0,[z0,z1,z61,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z381]),(0,[z0,z1,z2,z4,z5,z382,z6])],[(0,[z73,z0,z1,z2,z4,z5,z93]),(0,[z0,z1,z2,z383,z4,z5,z6]),(0,[z0,z1,z384,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z385]),(0,[z0,z1,z2,z4,z5,z6,z386])]],
   [[(0,[z0,z1,z89,z2,z4,z5,z6]),(0,[z0,z1,z387,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z27,z6]),(0,[z0,z1,z2,z4,z388,z5,z6]),(0,[z0,z389,z1,z2,z4,z5,z6])],[(0,[z88,z0,z1,z2,z4,z5,z6]),(0,[z390,z0,z1,z2,z4,z5,z6]),(0,[z59,z0,z1,z2,z4,z65,z6]),(0,[z0,z1,z172,z4,z5,z6,z49])],[(0,[z0,z1,z2,z4,z5,z391,z6]),(0,[z0,z1,z156,z2,z4,z5,z44])],[(0,[z341,z0,z1,z2,z4,z345,z6]),(0,[z0,z1,z392,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z393]),(0,[z0,z1,z394,z2,z4,z5,z6])],[(0,[z54,z0,z1,z2,z4,z5,z6])],[(0,[z9,z92,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z395]),(0,[z0,z1,z2,z4,z5,z6,z396]),(0,[z397,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z37,z2,z4,z5,z6])],[(0,[z0,z1,z2,z398,z4,z5,z6]),(0,[z0,z1,z399,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z400,z6]),(0,[z401,z0,z1,z2,z4,z5,z6]),(0,[z0,z402,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z403,z6]),(0,[z0,z1,z404,z2,z4,z5,z6]),(0,[z0,z1,z405,z2,z4,z5,z6]),(1,[z0,z1,z156,z117,z2,z4])]],
   [[(0,[z0,z1,z2,z4,z5,z406,z6])],[(0,[z407,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z77,z4,z5,z6,z211]),(0,[z0,z1,z2,z4,z151,z5,z6]),(0,[z146,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z408,z2,z4,z5,z6])],[(0,[z0,z1,z2,z409,z4,z5,z6]),(0,[z0,z1,z2,z4,z410,z5,z6]),(0,[z411,z0,z1,z2,z4,z5,z6]),(0,[z412,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z172,z76,z2,z5,z6])],[(0,[z0,z1,z2,z4,z4,z5,z6]),(1,[z0,z268,z178,z4,z5,z6]),(0,[z0,z1,z413,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z414]),(0,[z415,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z416]),(0,[z0,z1,z2,z417,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z418]),(1,[z0,z1,z419,z4,z5,z6])],[(0,[z0,z1,z2,z4,z420,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z421]),(0,[z0,z1,z422,z2,z4,z5,z6]),(0,[z0,z1,z2,z423,z4,z5,z6]),(0,[z0,z424,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z425,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z65,z5,z60,z6]),(0,[z0,z1,z2,z316,z4,z5,z6]),(0,[z0,z1,z140,z2,z71,z4,z6])],[(0,[z0,z1,z426,z2,z4,z5,z6]),(0,[z0,z113,z1,z2,z4,z171,z6]),(0,[z0,z1,z156,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z43,z44])],[(0,[z125,z88,z1,z2,z4,z5,z6]),(0,[z0,z1,z427,z2,z4,z5,z6]),(0,[z0,z1,z37,z2,z4,z65,z6]),(0,[z0,z1,z2,z4,z5,z428,z6]),(0,[z0,z429,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z430,z4,z5,z6])],[(1,[z74,z1,z2,z4,z5,z83]),(0,[z431,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z432]),(1,[z107,z0,z2,z4,z5,z62]),(0,[z0,z1,z346,z2,z71,z5,z6]),(0,[z433,z0,z1,z2,z4,z5,z6])],[(0,[z0,z434,z1,z2,z4,z5,z6]),(0,[z435,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z436,z2,z4,z5,z6]),(1,[z0,z1,z140,z4,z6,z49]),(0,[z437,z0,z1,z2,z4,z5,z6])],[(1,[z92,z197,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z438,z5,z6]),(0,[z0,z439,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z42,z6])],[(0,[z0,z1,z440,z2,z4,z5,z6]),(0,[z441,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z71,z4,z171,z6]),(0,[z0,z442,z1,z2,z4,z5,z6]),(0,[z0,z1,z55,z2,z4,z5,z6]),(0,[z443,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z117,z2,z4,z5,z6])],[(0,[z0,z1,z444,z2,z4,z5,z6]),(0,[z0,z26,z1,z2,z16,z5,z6]),(0,[z0,z1,z2,z445,z4,z5,z6]),(0,[z0,z1,z2,z4,z53,z6,z38]),(0,[z0,z1,z2,z147,z4,z5,z109]),(0,[z446,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z341,z0,z1,z2,z4,z371,z6]),(0,[z207,z0,z1,z178,z4,z5,z6]),(0,[z0,z1,z447,z2,z4,z5,z6]),(0,[z448,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z449,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z450,z6]),(0,[z0,z1,z451,z2,z4,z5,z6]),(0,[z0,z452,z1,z2,z4,z5,z6]),(0,[z0,z1,z453,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z360,z5,z6])],[(0,[z454,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z455,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z456]),(0,[z457,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z458,z4,z5,z6])],[(0,[z0,z1,z459,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z460]),(0,[z0,z1,z84,z2,z4,z5,z6]),(0,[z0,z1,z124,z2,z31,z5,z6])],[(0,[z0,z1,z2,z461,z4,z5,z6]),(0,[z0,z1,z462,z2,z4,z5,z6]),(0,[z0,z1,z2,z463,z4,z5,z6]),(0,[z0,z1,z117,z2,z4,z43,z5])],[(0,[z464,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z465,z2,z4,z5,z6]),(0,[z466,z0,z1,z2,z4,z5,z6])],[(0,[z467,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z468]),(0,[z0,z469,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z470,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z56,z6])],[(0,[z0,z1,z2,z471,z4,z5,z6]),(0,[z207,z0,z1,z2,z4,z428,z6]),(0,[z0,z113,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z472,z4,z5,z6]),(0,[z146,z0,z1,z147,z4,z5,z6]),(0,[z0,z1,z76,z37,z2,z5,z6])],[(0,[z0,z1,z70,z2,z4,z5,z6]),(0,[z0,z1,z2,z473,z4,z5,z6]),(1,[z0,z1,z84,z4,z5,z85])],[(1,[z64,z1,z2,z4,z65,z6]),(0,[z474,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z49]),(0,[z0,z1,z2,z71,z151,z5,z6]),(0,[z0,z1,z475,z2,z4,z5,z6])],[(0,[z0,z1,z76,z2,z4,z5,z6])],[(0,[z476,z0,z1,z2,z4,z5,z6]),(0,[z0,z477,z1,z2,z4,z5,z6]),(0,[z0,z1,z478,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z479]),(0,[z0,z1,z2,z480,z4,z5,z6]),(0,[z0,z1,z2,z71,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z109])],[(0,[z481,z0,z1,z2,z4,z5,z6]),(1,[z9,z61,z2,z4,z5,z6]),(0,[z482,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z483,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z484,z5,z6])]],
   [[(0,[z0,z1,z172,z70,z4,z5,z6]),(0,[z0,z1,z485,z2,z4,z5,z6])],[(0,[z74,z1,z61,z2,z4,z5,z6]),(0,[z59,z0,z1,z2,z4,z60,z6]),(0,[z0,z1,z2,z4,z5,z83,z6]),(0,[z0,z1,z2,z4,z17,z5,z6]),(0,[z0,z1,z2,z486,z4,z5,z6]),(0,[z0,z113,z2,z4,z5,z53,z6]),(0,[z0,z1,z2,z487,z4,z5,z6]),(0,[z0,z1,z30,z2,z147,z4,z5])],[(0,[z207,z0,z268,z2,z4,z5,z6]),(0,[z0,z1,z488,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z82,z6,z62]),(0,[z0,z1,z2,z489,z4,z5,z6]),(0,[z0,z1,z2,z4,z490,z5,z6])],[(0,[z491,z0,z1,z2,z4,z5,z6]),(0,[z492,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z493,z5,z6])],[(0,[z92,z0,z61,z2,z4,z5,z6]),(0,[z0,z1,z494,z2,z4,z5,z6]),(0,[z0,z1,z495,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z496]),(0,[z0,z1,z2,z497,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z44])],[(0,[z0,z1,z498,z2,z4,z5,z6]),(1,[z125,z1,z177,z4,z5,z6]),(0,[z0,z1,z357,z2,z4,z5,z6]),(0,[z499,z0,z1,z2,z4,z5,z6]),(0,[z0,z500,z1,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z4,z501,z5,z6]),(0,[z73,z1,z2,z4,z5,z6,z93]),(0,[z74,z0,z1,z2,z4,z5,z83]),(0,[z136,z0,z1,z2,z4,z5,z6])]],
   [[],[(0,[z0,z1,z2,z4,z5,z278,z6]),(0,[z107,z74,z0,z1,z2,z4,z5])],[(0,[z502,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z503,z6]),(0,[z0,z1,z2,z71,z4,z65,z6]),(0,[z0,z1,z504,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z208,z5,z6]),(0,[z0,z1,z505,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z506]),(0,[z0,z1,z2,z4,z5,z6,z507]),(0,[z0,z1,z2,z4,z5,z6,z508])],[(0,[z0,z1,z2,z509,z4,z5,z6])],[(0,[z0,z1,z2,z510,z4,z5,z6]),(0,[z0,z1,z2,z48,z71,z4,z6]),(0,[z0,z1,z124,z30,z2,z5,z6])],[(0,[z0,z1,z2,z4,z5,z511,z6]),(0,[z0,z1,z2,z4,z5,z6,z512]),(0,[z0,z1,z2,z513,z4,z5,z6])],[(0,[z514,z0,z1,z2,z4,z5,z6]),(1,[z429,z1,z2,z4,z5,z6]),(0,[z0,z1,z241,z2,z4,z5,z6]),(0,[z0,z1,z515,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z278]),(0,[z0,z1,z2,z4,z5,z6,z516]),(0,[z0,z268,z1,z178,z4,z5,z6]),(0,[z0,z1,z517,z2,z4,z5,z6])],[(0,[z88,z1,z89,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z345,z6]),(0,[z0,z1,z518,z2,z4,z5,z6]),(0,[z0,z1,z519,z2,z4,z5,z6])],[(0,[z0,z520,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z521,z4,z5,z6]),(0,[z0,z1,z2,z522,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z523])],[(0,[z524,z0,z1,z2,z4,z5,z6])],[(0,[z0,z268,z178,z2,z4,z5,z6]),(0,[z0,z1,z71,z4,z5,z6,z49])],[(1,[z149,z0,z1,z2,z4,z5]),(0,[z0,z1,z172,z2,z5,z6,z211]),(0,[z0,z525,z1,z2,z4,z5,z6])],[(0,[z526,z0,z1,z2,z4,z5,z6]),(0,[z527,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z528,z4,z5,z6]),(0,[z0,z1,z2,z4,z529,z5,z6]),(0,[z0,z1,z530,z2,z4,z5,z6]),(0,[z0,z1,z2,z531,z4,z5,z6]),(0,[z0,z137,z2,z4,z5,z82,z6])],[(0,[z0,z1,z532,z2,z4,z5,z6]),(0,[z533,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z534,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z535]),(0,[z0,z1,z2,z77,z4,z5,z6]),(0,[z536,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z31,z4,z5,z6])]],
   [[(0,[z537,z0,z1,z2,z4,z5,z6]),(0,[z538,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z539,z6]),(0,[z0,z1,z540,z2,z4,z5,z6])],[(0,[z0,z1,z2,z541,z4,z5,z6]),(1,[z0,z1,z241,z2,z4,z6])],[(0,[z542,z0,z1,z2,z4,z5,z6]),(0,[z543,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z544]),(0,[z0,z545,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z546,z4,z5,z6]),(0,[z0,z1,z2,z4,z547,z5,z6])],[(0,[z0,z1,z156,z2,z4,z43,z6])],[(0,[z0,z1,z548,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z93,z62]),(0,[z0,z1,z76,z2,z48,z5,z6]),(1,[z0,z1,z2,z31,z5,z109])],[(0,[z549,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z550,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z178,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z85]),(0,[z0,z1,z551,z2,z4,z5,z6])],[(0,[z0,z552,z1,z2,z4,z5,z6]),(0,[z553,z0,z1,z2,z4,z5,z6]),(0,[z554,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z555])],[(0,[z556,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z557]),(0,[z558,z0,z1,z2,z4,z5,z6]),(0,[z559,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z48,z5,z6,z38])],[(0,[z125,z0,z1,z2,z4,z127,z6]),(0,[z0,z1,z2,z4,z5,z560,z6]),(0,[z561,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z562,z2,z4,z5,z6])],[(0,[z563,z0,z1,z2,z4,z5,z6]),(0,[z564,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z565,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z93]),(0,[z0,z1,z172,z2,z77,z5,z6])],[(0,[z0,z26,z1,z2,z17,z5,z6]),(0,[z0,z1,z2,z4,z5,z566,z6]),(0,[z0,z1,z37,z276,z4,z5,z6]),(0,[z567,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z371,z6]),(0,[z0,z1,z2,z4,z568,z5,z6]),(0,[z0,z1,z76,z55,z2,z5,z6]),(0,[z0,z1,z2,z569,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z570,z6]),(0,[z571,z0,z1,z2,z4,z5,z6]),(0,[z572,z0,z1,z2,z4,z5,z6]),(0,[z573,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z70,z2,z4,z6,z38])]],
   [[(0,[z574,z0,z1,z2,z4,z5,z6]),(0,[z575,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z140,z37,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z576])],[(0,[z0,z1,z2,z4,z5,z6,z93]),(0,[z0,z577,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z578,z5,z6]),(0,[z0,z1,z2,z579,z4,z5,z6]),(0,[z0,z1,z76,z2,z4,z6,z38])],[(0,[z0,z580,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z104,z6]),(0,[z0,z1,z581,z2,z4,z5,z6])],[(0,[z0,z1,z2,z582,z4,z5,z6]),(0,[z0,z1,z583,z2,z4,z5,z6]),(0,[z0,z185,z1,z2,z4,z5,z6]),(0,[z584,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z585])],[(0,[z0,z1,z2,z4,z5,z6,z586]),(0,[z74,z1,z2,z4,z5,z83,z6]),(0,[z0,z1,z2,z4,z587,z5,z6]),(0,[z0,z1,z588,z2,z4,z5,z6]),(0,[z0,z1,z419,z2,z4,z5,z6])],[(0,[z125,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z589,z5,z6])],[(0,[z0,z590,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z591,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z592,z6]),(0,[z593,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z346,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z594]),(0,[z595,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z82,z6]),(0,[z0,z1,z2,z4,z5,z6,z596])]],
   [[(0,[z0,z197,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z597,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z598]),(0,[z599,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z600]),(1,[z54,z0,z2,z16,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z601]),(0,[z0,z602,z1,z2,z4,z5,z6]),(0,[z146,z0,z1,z2,z4,z5,z85]),(0,[z0,z1,z603,z2,z4,z5,z6])],[(0,[z92,z197,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z604,z5,z6]),(0,[z0,z1,z605,z2,z4,z5,z6]),(0,[z0,z1,z419,z37,z4,z5,z6])],[(0,[z606,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z607]),(1,[z0,z1,z2,z4,z428,z6]),(0,[z0,z1,z2,z608,z4,z5,z6]),(0,[z609,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z610,z2,z4,z5,z6])],[(0,[z0,z1,z611,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z612]),(0,[z0,z1,z2,z4,z5,z6,z613]),(0,[z0,z1,z2,z4,z5,z6,z614]),(0,[z0,z1,z2,z4,z5,z615,z6])],[(0,[z21,z0,z1,z2,z32,z5,z6]),(0,[z0,z1,z616,z2,z4,z5,z6])],[(0,[z0,z1,z100,z2,z4,z5,z6]),(0,[z0,z1,z2,z617,z4,z5,z6])],[]],
   [[(0,[z0,z1,z2,z4,z60,z6,z38]),(0,[z95,z0,z1,z2,z4,z53,z6]),(0,[z618,z0,z1,z2,z4,z5,z6]),(0,[z619,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z620,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z621,z0,z1,z2,z4,z5,z6]),(1,[z136,z1,z2,z4,z5,z6]),(0,[z622,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z127,z5,z6]),(0,[z0,z1,z2,z623,z4,z5,z6]),(0,[z624,z0,z1,z2,z4,z5,z6])],[(0,[z0,z625,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z626]),(0,[z627,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z628]),(0,[z0,z1,z629,z2,z4,z5,z6]),(0,[z630,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z631,z2,z4,z5,z6])],[(0,[z632,z0,z1,z2,z4,z5,z6]),(0,[z0,z26,z1,z2,z4,z104,z6]),(0,[z0,z1,z2,z4,z633,z5,z6]),(0,[z634,z0,z1,z2,z4,z5,z6])],[(0,[z0,z197,z2,z4,z5,z6,z62]),(0,[z0,z1,z635,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z636,z5,z6]),(0,[z0,z1,z140,z2,z4,z6,z49]),(0,[z0,z1,z2,z4,z5,z6,z637]),(0,[z0,z638,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z639]),(0,[z0,z1,z2,z4,z5,z6,z640])],[(0,[z0,z1,z641,z2,z4,z5,z6]),(0,[z0,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z642,z2,z4,z5,z6]),(0,[z0,z1,z2,z643,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z644]),(0,[z0,z1,z2,z4,z5,z6,z645])]],
   [[(0,[z1,z2,z22,z4,z32,z5,z6]),(0,[z0,z1,z2,z646,z4,z5,z6]),(0,[z0,z1,z2,z4,z647,z5,z6]),(0,[z0,z1,z648,z2,z4,z5,z6])],[(1,[z0,z1,z172,z5,z6,z211])],[(0,[z149,z0,z1,z2,z4,z5,z6]),(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z88,z0,z1,z177,z4,z5,z6]),(0,[z0,z1,z2,z22,z4,z5,z6]),(0,[z0,z1,z650,z2,z4,z5,z6])],[],[(0,[z74,z92,z1,z2,z4,z5,z6]),(0,[z73,z107,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z651,z6]),(0,[z0,z1,z84,z2,z4,z5,z85]),(0,[z0,z1,z2,z4,z5,z652,z6])],[(0,[z0,z1,z2,z4,z653,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z654]),(0,[z0,z1,z2,z4,z655,z5,z6]),(0,[z341,z0,z1,z2,z22,z5,z6]),(0,[z0,z1,z656,z2,z4,z5,z6])],[(0,[z197,z1,z61,z2,z4,z5,z6]),(0,[z0,z1,z657,z2,z4,z5,z6]),(0,[z73,z0,z185,z2,z4,z5,z6]),(0,[z0,z1,z658,z2,z4,z5,z6]),(0,[z659,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z660,z4,z5,z6])],[(1,[z207,z0,z179,z4,z5,z6]),(0,[z0,z661,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z85,z109])]],
   [[(0,[z207,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z662]),(0,[z21,z341,z1,z2,z4,z5,z6]),(0,[z663,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z664,z2,z4,z5,z6]),(0,[z0,z1,z665,z2,z4,z5,z6])],[(0,[z0,z1,z666,z2,z4,z5,z6]),(0,[z667,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z668,z5,z6]),(0,[z669,z0,z1,z2,z4,z5,z6]),(0,[z0,z670,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z671,z4,z5,z6]),(0,[z0,z1,z2,z4,z65,z6,z49]),(0,[z0,z1,z672,z2,z4,z5,z6]),(0,[z0,z26,z1,z2,z4,z5,z6]),(0,[z0,z1,z673,z2,z4,z5,z6])],[(0,[z341,z0,z1,z2,z4,z5,z6]),(0,[z674,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z230]),(0,[z0,z1,z2,z4,z5,z6,z675]),(0,[z146,z0,z1,z84,z4,z5,z6])],[],[(0,[z0,z1,z2,z4,z5,z676,z6]),(0,[z341,z1,z2,z4,z32,z5,z6]),(0,[z677,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z171,z6,z49])],[(0,[z0,z1,z678,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z83,z6,z93]),(0,[z0,z137,z1,z2,z4,z5,z62])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z679]),(0,[z107,z429,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z316,z4,z6]),(0,[z0,z1,z2,z4,z680,z5,z6])],[(0,[z0,z1,z2,z681,z4,z5,z6]),(0,[z0,z1,z172,z2,z4,z5,z230]),(0,[z0,z1,z2,z682,z4,z5,z6])],[(0,[z0,z1,z683,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z684]),(0,[z685,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z686,z4,z5,z6]),(0,[z0,z1,z687,z2,z4,z5,z6]),(0,[z54,z0,z26,z2,z4,z5,z6]),(0,[z0,z688,z1,z2,z4,z5,z6]),(0,[z0,z1,z689,z2,z4,z5,z6]),(0,[z690,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z691])],[(0,[z0,z692,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z693,z4,z5,z6]),(0,[z0,z1,z2,z694,z4,z5,z6])],[(0,[z0,z1,z37,z2,z4,z60,z6]),(0,[z0,z1,z695,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z696,z6]),(0,[z0,z1,z697,z2,z4,z5,z6])],[(0,[z9,z0,z197,z2,z4,z5,z6]),(0,[z0,z1,z2,z698,z4,z5,z6]),(0,[z0,z699,z1,z2,z4,z5,z6]),(0,[z700,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z701]),(0,[z0,z1,z702,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z703,z6]),(0,[z704,z0,z1,z2,z4,z5,z6]),(0,[z705,z0,z1,z2,z4,z5,z6]),(0,[z706,z0,z1,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z54,z0,z2,z16,z5,z6]),(0,[z0,z1,z172,z5,z230,z211])],[(0,[z0,z1,z2,z4,z707,z6]),(0,[z149,z0,z2,z4,z5,z62]),(0,[z0,z1,z708,z4,z5,z6]),(0,[z0,z2,z4,z5,z82,z709]),(0,[z0,z1,z710,z4,z5,z6])],[(0,[z0,z1,z711,z2,z4,z5]),(0,[z0,z1,z2,z4,z712,z6]),(0,[z0,z1,z713,z4,z5,z6]),(0,[z0,z1,z2,z4,z428,z6]),(0,[z107,z136,z2,z4,z5,z62]),(0,[z0,z1,z2,z4,z714,z6]),(0,[z0,z1,z4,z715,z6,z49])],[(0,[z0,z716,z2,z4,z5,z6]),(0,[z0,z1,z2,z151,z60,z6]),(0,[z553,z1,z2,z4,z5,z83])]],
   [[(0,[z0,z1,z2,z4,z717,z6]),(0,[z0,z1,z2,z4,z718,z6]),(0,[z0,z1,z2,z4,z5,z719]),(0,[z0,z1,z2,z4,z56,z6]),(0,[z0,z1,z2,z4,z720,z6]),(0,[z0,z1,z721,z2,z31,z5])],[(0,[z149,z0,z357,z2,z4,z5]),(0,[z0,z1,z2,z722,z4,z6]),(0,[z0,z2,z723,z4,z5,z6])],[(0,[z0,z137,z2,z4,z5,z82])],[(0,[z724,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z725,z4,z5,z6]),(0,[z0,z1,z2,z4,z726,z6]),(0,[z0,z1,z2,z4,z727,z6]),(1,[z1,z2,z4,z5,z728]),(0,[z0,z1,z172,z729,z5,z6]),(0,[z0,z1,z2,z142,z5,z109])],[(0,[z0,z1,z730,z2,z5,z6]),(0,[z0,z1,z731,z2,z4,z5]),(0,[z0,z1,z377,z4,z6,z49]),(0,[z74,z357,z2,z4,z5,z6]),(0,[z0,z26,z2,z732,z5,z6]),(0,[z0,z1,z2,z4,z5,z709]),(0,[z0,z1,z733,z2,z5,z6]),(0,[z146,z0,z1,z147,z4,z5])],[(0,[z0,z1,z734,z4,z5,z6]),(0,[z0,z1,z735,z4,z5,z6]),(0,[z1,z2,z4,z5,z83,z728]),(0,[z221,z0,z1,z4,z6,z49])],[(0,[z415,z1,z2,z4,z5,z93]),(0,[z0,z1,z2,z4,z736,z6]),(0,[z0,z1,z562,z37,z2,z6]),(0,[z0,z1,z2,z4,z737,z6]),(0,[z0,z113,z2,z4,z738,z6]),(0,[z0,z1,z172,z76,z6,z49]),(0,[z0,z1,z2,z151,z5,z6]),(0,[z0,z1,z123,z2,z6,z38])]],
   [[(0,[z1,z2,z4,z739,z5,z6]),(0,[z740,z0,z2,z4,z5,z6]),(0,[z429,z137,z2,z4,z5,z6]),(0,[z0,z1,z76,z2,z388,z6]),(0,[z0,z1,z55,z77,z42,z6])],[(0,[z0,z1,z2,z741,z5,z6]),(0,[z690,z0,z2,z4,z171,z6]),(0,[z0,z1,z419,z76,z37,z6])],[(0,[z0,z1,z156,z742,z2,z4]),(0,[z0,z1,z117,z742,z2,z4])],[(0,[z0,z1,z743,z4,z5,z6]),(0,[z0,z1,z2,z4,z744,z6]),(0,[z0,z1,z2,z4,z745,z6]),(0,[z1,z357,z2,z4,z5,z93]),(0,[z746,z1,z2,z4,z5,z6]),(0,[z429,z1,z2,z4,z5,z62])]],
   [[(0,[z0,z1,z2,z4,z747,z6]),(0,[z0,z1,z748,z4,z5,z6]),(0,[z0,z1,z749,z2,z4,z6]),(0,[z0,z1,z750,z4,z5,z6])],[(0,[z0,z1,z2,z4,z751,z6]),(0,[z0,z1,z140,z2,z151,z6]),(0,[z0,z1,z76,z2,z151,z6])],[(0,[z0,z752,z2,z4,z5,z6]),(0,[z244,z1,z2,z4,z5,z93]),(0,[z0,z1,z2,z753,z5,z6]),(0,[z0,z1,z2,z732,z5,z6]),(0,[z0,z1,z2,z4,z754,z6])],[(0,[z0,z755,z2,z4,z5,z6]),(0,[z1,z2,z734,z4,z5,z6]),(0,[z0,z1,z2,z4,z739,z6]),(0,[z74,z1,z2,z4,z5,z728]),(0,[z0,z1,z723,z4,z5,z6]),(0,[z0,z1,z2,z756,z5,z6]),(0,[z0,z26,z2,z17,z104,z6]),(0,[z0,z1,z172,z343,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z757]),(0,[z0,z1,z2,z4,z758,z6]),(0,[z0,z1,z2,z759,z4,z6])],[(0,[z0,z1,z2,z4,z760,z6]),(0,[z0,z1,z2,z4,z761,z6])],[(0,[z0,z1,z2,z762,z5,z6]),(0,[z0,z1,z763,z4,z5,z6]),(0,[z207,z0,z179,z4,z5,z6])],[(0,[z73,z1,z2,z4,z5,z93]),(0,[z0,z1,z764,z4,z5,z6]),(1,[z0,z1,z729,z5,z6]),(0,[z0,z1,z2,z4,z765,z6]),(0,[z0,z1,z55,z77,z56,z6])]],
   [[(0,[z0,z1,z2,z151,z65,z6]),(0,[z0,z1,z2,z4,z766,z6]),(0,[z0,z1,z2,z767,z5,z6]),(0,[z0,z1,z453,z71,z4,z6])],[(0,[z0,z185,z2,z4,z5,z6]),(0,[z9,z61,z2,z4,z5,z278]),(0,[z0,z1,z2,z4,z768,z6]),(0,[z0,z1,z2,z4,z769,z6]),(0,[z0,z1,z98,z71,z4,z6]),(0,[z0,z1,z2,z4,z5,z770]),(0,[z0,z1,z76,z2,z771,z6])],[(0,[z0,z1,z2,z4,z5,z772]),(0,[z0,z1,z2,z4,z773,z6]),(0,[z0,z774,z2,z4,z5,z6]),(1,[z357,z2,z4,z5,z93]),(0,[z0,z137,z656,z2,z4,z5]),(0,[z0,z2,z16,z732,z5,z6]),(0,[z0,z1,z2,z729,z5,z6])],[(0,[z0,z113,z2,z4,z53,z6]),(0,[z0,z1,z2,z4,z5,z230]),(0,[z775,z1,z2,z4,z5,z6]),(0,[z0,z1,z776,z2,z4,z5]),(0,[z0,z1,z84,z777,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z278]),(0,[z0,z1,z2,z4,z5,z778]),(0,[z0,z1,z2,z4,z126,z6]),(0,[z0,z1,z2,z779,z5,z6]),(0,[z0,z2,z4,z171,z738,z6]),(0,[z0,z1,z2,z4,z360,z5]),(0,[z0,z1,z2,z316,z6,z38]),(0,[z0,z1,z2,z780,z5,z6])],[(0,[z0,z1,z781,z4,z5,z6]),(0,[z782,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z783,z5]),(0,[z0,z1,z784,z4,z5,z6]),(0,[z0,z1,z55,z36,z5,z6]),(0,[z0,z1,z70,z346,z71,z6])],[(0,[z0,z357,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z785,z6]),(0,[z125,z1,z177,z4,z126,z6]),(0,[z0,z1,z2,z316,z4,z6]),(0,[z0,z1,z2,z4,z715,z6]),(0,[z0,z1,z2,z48,z6,z38])]],
   [[(0,[z0,z786,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z787,z6]),(0,[z0,z1,z742,z2,z4,z5])],[(0,[z149,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z788,z6]),(0,[z0,z1,z55,z241,z77,z6]),(0,[z0,z1,z2,z789,z5,z6])],[(0,[z790,z61,z2,z4,z5,z6]),(0,[z0,z1,z2,z791,z5,z6]),(0,[z0,z26,z2,z17,z5,z6]),(0,[z0,z1,z729,z5,z6,z211]),(0,[z0,z1,z241,z276,z4,z6]),(0,[z0,z1,z2,z771,z48,z6])],[(0,[z0,z1,z2,z4,z792,z6]),(0,[z0,z1,z55,z2,z42,z6])]],
   [[(0,[z149,z1,z2,z4,z5,z93]),(0,[z0,z1,z2,z4,z793,z6]),(0,[z0,z1,z2,z794,z5,z6]),(1,[z1,z2,z795,z5,z6]),(0,[z0,z796,z2,z4,z5,z6]),(0,[z0,z797,z2,z4,z5,z6]),(0,[z0,z1,z798,z4,z5,z6]),(0,[z0,z1,z721,z2,z5,z6])],[(0,[z0,z1,z2,z4,z5,z799]),(0,[z0,z1,z2,z4,z800,z5]),(0,[z0,z1,z241,z2,z4,z6]),(0,[z0,z1,z70,z2,z151,z6])],[(0,[z0,z1,z2,z4,z5,z801]),(0,[z0,z1,z2,z4,z5,z802]),(0,[z0,z803,z2,z4,z5,z6]),(0,[z804,z1,z2,z4,z5,z6]),(0,[z0,z1,z805,z4,z5,z6]),(0,[z0,z1,z806,z4,z5,z6])],[(0,[z357,z2,z4,z5,z6,z93]),(0,[z1,z2,z4,z5,z728,z93]),(0,[z807,z1,z2,z4,z5,z6]),(0,[z0,z1,z473,z4,z6,z49])]],
   [[(0,[z0,z1,z2,z4,z5,z808]),(0,[z0,z1,z809,z2,z5,z6]),(0,[z0,z810,z2,z4,z5,z6]),(0,[z0,z1,z2,z811,z5,z6]),(0,[z0,z1,z812,z2,z4,z6]),(0,[z0,z1,z2,z813,z5,z6]),(0,[z429,z2,z4,z5,z6,z62]),(0,[z0,z1,z721,z2,z4,z5])],[(0,[z0,z1,z814,z4,z5,z6])],[(0,[z0,z1,z2,z4,z815,z6])],[(0,[z0,z1,z2,z4,z816,z6]),(0,[z0,z2,z4,z5,z6,z817]),(0,[z0,z1,z55,z77,z316,z6]),(0,[z0,z1,z76,z159,z2,z6])]],
   [[(0,[z74,z1,z2,z4,z5,z503]),(1,[z1,z734,z4,z5,z6])],[(0,[z0,z1,z2,z818,z5,z6]),(0,[z0,z1,z2,z4,z819,z6]),(0,[z0,z1,z820,z4,z5,z6]),(0,[z0,z1,z631,z4,z5,z85])],[(0,[z0,z1,z2,z4,z821,z6])],[(0,[z0,z1,z2,z822,z5,z6]),(0,[z0,z1,z2,z4,z5,z823]),(0,[z0,z1,z2,z824,z5,z6]),(0,[z0,z1,z2,z4,z825,z6]),(0,[z0,z2,z4,z738,z5,z6]),(0,[z0,z1,z475,z30,z2,z5]),(0,[z0,z1,z742,z2,z4,z43])]],
   [[(0,[z0,z1,z826,z4,z5,z6]),(1,[z0,z2,z4,z5,z709]),(0,[z0,z1,z551,z4,z6,z49]),(0,[z0,z1,z2,z777,z4,z5])],[(0,[z92,z129,z2,z4,z5,z6]),(1,[z0,z1,z2,z771,z6])],[(0,[z0,z2,z4,z5,z6,z827]),(0,[z0,z1,z2,z4,z828,z6]),(1,[z0,z1,z742,z2,z4])],[(0,[z829,z0,z2,z4,z5,z6]),(0,[z165,z1,z2,z4,z65,z6])]],
   [[(0,[z0,z1,z2,z4,z830,z6]),(0,[z0,z1,z2,z831,z5,z6]),(0,[z0,z1,z419,z4,z5,z6]),(0,[z0,z832,z2,z4,z5,z6])],[(0,[z0,z1,z833,z2,z5,z6]),(0,[z0,z26,z2,z17,z27,z6]),(0,[z0,z2,z4,z738,z53,z6]),(0,[z0,z1,z172,z4,z56,z6]),(0,[z0,z1,z2,z4,z5,z834]),(0,[z0,z1,z77,z4,z56,z6]),(0,[z0,z1,z70,z346,z5,z6])],[(0,[z0,z1,z2,z4,z835,z5]),(0,[z0,z836,z1,z2,z4,z5]),(0,[z0,z1,z837,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z838]),(0,[z0,z1,z76,z37,z2,z6])],[(0,[z0,z137,z2,z4,z5,z709]),(0,[z0,z1,z70,z71,z4,z6]),(0,[z0,z1,z71,z4,z715,z6])]],
   [[(0,[z0,z1,z839,z2,z5,z6]),(0,[z0,z1,z2,z4,z840,z6]),(0,[z0,z1,z2,z4,z841,z6]),(0,[z0,z1,z2,z4,z43,z44])],[(0,[z74,z1,z131,z2,z4,z5]),(0,[z842,z1,z2,z4,z5,z6]),(1,[z0,z2,z732,z5,z6])],[(0,[z0,z1,z843,z2,z4,z5]),(0,[z0,z844,z2,z4,z5,z6]),(1,[z0,z723,z4,z5,z6]),(0,[z0,z1,z845,z2,z4,z6]),(0,[z0,z1,z70,z241,z4,z6])],[(0,[z0,z1,z2,z4,z846,z6]),(0,[z0,z137,z2,z4,z5,z620]),(0,[z0,z1,z847,z2,z4,z6]),(0,[z0,z1,z2,z848,z4,z6]),(0,[z0,z1,z140,z4,z6,z49]),(0,[z0,z1,z2,z849,z5,z6])]],
   [[(0,[z92,z197,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z850,z6]),(0,[z851,z1,z2,z4,z5,z6]),(0,[z0,z1,z852,z4,z5,z6])],[(0,[z0,z1,z2,z4,z853,z6]),(0,[z0,z1,z2,z4,z854,z6]),(0,[z0,z2,z4,z5,z6,z855]),(0,[z0,z1,z742,z2,z4,z44])],[(0,[z0,z1,z2,z4,z5,z856]),(0,[z0,z1,z857,z4,z5,z6]),(0,[z0,z1,z2,z4,z858,z6]),(0,[z207,z0,z723,z4,z5,z6]),(0,[z0,z1,z419,z76,z5,z6])],[(0,[z92,z1,z2,z4,z5,z10]),(0,[z0,z1,z2,z859,z5,z6]),(0,[z0,z1,z860,z2,z5,z6]),(0,[z0,z1,z2,z597,z6,z38]),(0,[z0,z178,z723,z4,z5,z6])]],
   [[(0,[z9,z790,z2,z4,z5,z6]),(0,[z0,z1,z2,z861,z5,z6]),(0,[z0,z1,z241,z4,z6,z49])],[(1,[z790,z2,z4,z5,z6]),(0,[z1,z2,z4,z739,z60,z6])],[(0,[z355,z61,z2,z4,z5,z6]),(0,[z0,z1,z100,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z862]),(0,[z1,z89,z734,z4,z5,z6]),(0,[z0,z1,z2,z4,z863,z6]),(0,[z0,z1,z2,z4,z104,z6])],[(0,[z0,z1,z2,z4,z5,z864]),(0,[z9,z61,z2,z4,z5,z10]),(0,[z0,z1,z865,z2,z4,z5]),(0,[z0,z2,z732,z17,z5,z6]),(1,[z429,z2,z4,z5,z62]),(0,[z866,z1,z2,z4,z5,z6])]],
   [[(1,[z61,z2,z4,z5,z10]),(0,[z0,z1,z2,z4,z867,z6]),(0,[z868,z1,z2,z4,z5,z6])],[(0,[z136,z1,z2,z4,z5,z6]),(0,[z0,z1,z869,z2,z4,z6]),(0,[z0,z1,z2,z870,z4,z5]),(0,[z0,z1,z2,z795,z5,z6]),(0,[z0,z871,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z872,z6]),(0,[z873,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z10]),(0,[z0,z1,z2,z4,z5,z874]),(0,[z0,z875,z2,z4,z5,z6]),(0,[z0,z1,z276,z4,z171,z6]),(0,[z0,z1,z2,z4,z5,z876]),(0,[z0,z1,z124,z30,z2,z5])],[(0,[z0,z1,z2,z4,z127,z6]),(0,[z88,z1,z734,z4,z5,z6]),(0,[z207,z0,z179,z4,z428,z6]),(0,[z0,z1,z2,z4,z738,z6]),(0,[z0,z1,z140,z4,z715,z6]),(0,[z0,z1,z287,z147,z4,z5])]],
   [[(0,[z630,z197,z2,z4,z5,z6]),(0,[z0,z1,z2,z877,z4,z6]),(0,[z0,z1,z147,z777,z4,z5])],[(0,[z0,z1,z2,z878,z4,z6]),(0,[z0,z1,z84,z4,z5,z85])],[(0,[z0,z1,z2,z4,z879,z6]),(0,[z125,z1,z177,z4,z127,z6]),(0,[z0,z880,z2,z4,z5,z6]),(0,[z21,z1,z2,z795,z5,z6]),(0,[z64,z1,z2,z4,z65,z6]),(0,[z0,z1,z2,z881,z5,z6])],[(0,[z669,z1,z2,z4,z60,z6]),(0,[z0,z1,z882,z4,z5,z6]),(0,[z0,z1,z172,z70,z6,z38]),(0,[z0,z1,z77,z729,z5,z6])]],
   [[(0,[z0,z883,z2,z4,z5,z6]),(0,[z0,z1,z2,z771,z5,z6]),(0,[z0,z1,z742,z2,z4,z6])],[(0,[z0,z268,z723,z4,z5,z6]),(0,[z0,z1,z172,z5,z6,z211]),(0,[z0,z1,z55,z729,z5,z6])],[(0,[z9,z61,z2,z4,z5,z6]),(0,[z1,z734,z177,z4,z5,z6]),(0,[z0,z1,z276,z4,z60,z6]),(0,[z0,z1,z2,z4,z884,z6]),(0,[z885,z1,z2,z4,z5,z6]),(0,[z0,z1,z777,z4,z5,z85])],[(0,[z21,z1,z2,z22,z5,z6]),(0,[z0,z1,z2,z886,z5,z6]),(0,[z1,z2,z4,z5,z6,z887])]],
   [[(0,[z0,z1,z888,z2,z4,z5]),(0,[z889,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z890,z4,z5,z6])],[(0,[z0,z1,z2,z4,z891,z6]),(0,[z0,z892,z2,z4,z5,z6]),(0,[z0,z1,z721,z2,z5,z109])],[(0,[z0,z1,z2,z893,z5,z6]),(0,[z0,z1,z2,z4,z5,z894]),(0,[z0,z1,z2,z4,z895,z6]),(0,[z73,z1,z2,z4,z5,z728]),(0,[z0,z1,z2,z316,z151,z6]),(0,[z0,z1,z2,z4,z896,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z897]),(0,[z125,z1,z177,z4,z5,z6]),(0,[z341,z1,z2,z795,z5,z6]),(0,[z0,z1,z898,z4,z5,z6]),(0,[z0,z1,z2,z151,z53,z6]),(0,[z107,z429,z2,z4,z5,z62]),(0,[z0,z1,z346,z2,z5,z6]),(0,[z0,z1,z123,z71,z4,z6]),(0,[z146,z0,z1,z777,z4,z5])],[(0,[z0,z1,z899,z4,z5,z6]),(0,[z0,z1,z2,z4,z900,z6]),(0,[z0,z1,z4,z729,z5,z6])],[(0,[z0,z901,z1,z2,z4,z5]),(0,[z1,z2,z4,z5,z6,z902]),(0,[z0,z1,z276,z4,z5,z6]),(0,[z0,z1,z2,z48,z151,z6])],[(0,[z0,z1,z903,z2,z5,z6]),(0,[z0,z1,z70,z36,z4,z6])]],
   [[(0,[z244,z61,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z904,z6]),(0,[z0,z1,z2,z4,z208,z6]),(0,[z0,z1,z2,z4,z905,z6])],[(0,[z0,z1,z2,z4,z906,z6]),(0,[z0,z1,z907,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z728]),(0,[z0,z1,z908,z4,z5,z6]),(0,[z0,z1,z124,z721,z2,z5])],[(0,[z909,z1,z2,z4,z5,z6]),(0,[z54,z0,z2,z732,z5,z6]),(0,[z0,z1,z910,z2,z4,z6]),(0,[z0,z1,z140,z276,z4,z6]),(0,[z0,z1,z76,z276,z4,z6])],[(0,[z61,z2,z4,z5,z6,z10]),(0,[z575,z61,z2,z4,z5,z6]),(0,[z92,z790,z2,z4,z5,z6]),(0,[z341,z1,z2,z32,z5,z6]),(0,[z0,z357,z2,z4,z5,z83]),(0,[z95,z0,z2,z4,z171,z6]),(0,[z0,z1,z70,z4,z715,z6]),(0,[z0,z1,z911,z4,z5,z6])]],
   [[(0,[z0,z1,z276,z4,z53,z6])],[(0,[z0,z1,z912,z2,z4,z6]),(0,[z913,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z914,z6]),(0,[z0,z389,z2,z4,z53,z6]),(0,[z0,z1,z37,z2,z473,z6])],[(0,[z429,z1,z2,z4,z5,z6]),(0,[z149,z74,z1,z2,z4,z5]),(0,[z88,z1,z89,z4,z5,z6]),(0,[z0,z1,z2,z915,z5,z6]),(0,[z0,z1,z172,z2,z42,z6])],[(0,[z1,z2,z795,z32,z5,z6]),(0,[z73,z185,z2,z4,z5,z93]),(0,[z916,z1,z2,z4,z5,z6]),(1,[z0,z1,z4,z715,z6])]],
   [[(0,[z0,z1,z2,z4,z345,z6]),(0,[z0,z1,z917,z4,z5,z6]),(0,[z207,z0,z179,z4,z208,z6])],[(0,[z95,z0,z2,z4,z738,z6])],[(0,[z0,z790,z2,z4,z5,z6])],[(0,[z9,z149,z61,z2,z4,z5]),(0,[z0,z1,z276,z4,z65,z6]),(0,[z0,z1,z2,z4,z918,z6]),(0,[z0,z1,z2,z4,z5,z919])]],
   [[(0,[z0,z1,z2,z4,z5,z920]),(0,[z1,z2,z795,z4,z5,z6]),(0,[z0,z1,z2,z4,z921,z6]),(0,[z0,z1,z2,z4,z27,z6]),(0,[z0,z429,z2,z4,z5,z62]),(0,[z0,z1,z55,z77,z5,z6])],[(0,[z0,z61,z2,z4,z5,z10]),(0,[z73,z357,z2,z4,z5,z93]),(0,[z922,z1,z2,z4,z5,z6]),(0,[z429,z1,z2,z4,z5,z82]),(0,[z0,z2,z4,z5,z6,z709])],[(0,[z0,z1,z2,z4,z5,z728]),(0,[z0,z1,z2,z4,z923,z6]),(0,[z0,z1,z2,z383,z6,z38])],[(0,[z125,z1,z734,z4,z5,z6]),(0,[z0,z924,z2,z4,z5,z6]),(0,[z1,z2,z22,z795,z5,z6]),(0,[z0,z1,z2,z4,z925,z6]),(0,[z0,z1,z217,z37,z2,z6]),(0,[z0,z1,z926,z4,z5,z6])]],
   [[(0,[z74,z137,z61,z2,z4,z5]),(0,[z0,z1,z2,z4,z927,z5]),(1,[z0,z1,z721,z2,z5])],[(0,[z0,z1,z928,z4,z5,z6]),(0,[z0,z2,z732,z4,z5,z6]),(0,[z0,z1,z159,z77,z5,z6]),(0,[z0,z1,z2,z929,z5,z6])],[(0,[z9,z100,z61,z2,z4,z5]),(0,[z0,z1,z2,z930,z4,z6]),(0,[z341,z1,z2,z32,z345,z6]),(0,[z0,z688,z2,z4,z53,z6]),(0,[z0,z1,z276,z48,z4,z6]),(0,[z0,z1,z76,z37,z276,z6])],[(0,[z91,z0,z2,z4,z5,z62]),(0,[z0,z1,z70,z71,z151,z6]),(0,[z0,z1,z156,z117,z2,z4])]],
   [[(0,[z0,z1,z2,z4,z931,z6]),(0,[z0,z1,z932,z2,z4,z6]),(0,[z221,z0,z1,z2,z6,z38]),(0,[z0,z1,z70,z4,z388,z6]),(0,[z0,z1,z2,z31,z5,z109])],[(0,[z0,z1,z2,z4,z933,z6])],[(0,[z74,z429,z1,z2,z4,z5]),(1,[z0,z2,z4,z738,z6]),(0,[z0,z1,z172,z360,z5,z211]),(0,[z0,z1,z2,z4,z934,z6]),(0,[z0,z1,z70,z276,z4,z6])],[(0,[z0,z1,z2,z4,z935,z6]),(0,[z0,z424,z2,z4,z171,z6]),(0,[z0,z2,z4,z5,z709,z62])]],
   [[(0,[z61,z2,z4,z5,z93,z62]),(0,[z0,z1,z936,z4,z5,z6]),(0,[z0,z268,z178,z4,z5,z6]),(0,[z937,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z938,z5,z6]),(1,[z0,z1,z777,z4,z5])],[(0,[z0,z1,z2,z4,z5,z939]),(0,[z59,z1,z2,z4,z60,z6]),(0,[z0,z137,z357,z2,z4,z5]),(0,[z73,z429,z1,z2,z4,z5]),(0,[z0,z1,z172,z14,z5,z6])],[(0,[z197,z790,z2,z4,z5,z6]),(1,[z1,z2,z4,z739,z6]),(0,[z575,z0,z2,z4,z5,z62]),(0,[z0,z1,z2,z4,z940,z6])],[(0,[z0,z941,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z942,z6]),(0,[z943,z1,z2,z4,z5,z6]),(0,[z0,z1,z419,z5,z6,z38])]],
   [[(0,[z0,z1,z2,z4,z944,z6]),(0,[z0,z1,z2,z4,z5,z945]),(0,[z0,z1,z76,z2,z316,z6]),(0,[z0,z1,z346,z5,z6,z49])],[(0,[z0,z197,z2,z4,z5,z10]),(0,[z0,z1,z2,z4,z946,z6]),(0,[z0,z1,z2,z4,z371,z6]),(0,[z0,z1,z352,z4,z6,z49]),(0,[z0,z1,z172,z5,z6,z544])],[(0,[z0,z1,z947,z2,z5,z6]),(0,[z0,z1,z2,z948,z5,z6]),(0,[z0,z1,z949,z2,z4,z6]),(0,[z0,z1,z2,z950,z4,z6]),(0,[z951,z1,z2,z4,z5,z6]),(0,[z0,z1,z952,z2,z4,z6]),(0,[z953,z1,z2,z4,z5,z6])],[(0,[z149,z0,z137,z2,z4,z5]),(0,[z0,z954,z2,z4,z5,z6]),(0,[z97,z1,z2,z4,z65,z6]),(0,[z74,z1,z2,z4,z5,z83]),(0,[z0,z1,z2,z4,z955,z6]),(0,[z107,z0,z2,z4,z5,z62]),(0,[z0,z1,z37,z2,z771,z6])]],
   [[(0,[z0,z1,z2,z4,z956,z6]),(0,[z0,z357,z2,z4,z5,z93])],[(0,[z0,z1,z2,z4,z5,z957]),(0,[z1,z790,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z958,z6]),(0,[z0,z723,z179,z4,z5,z6]),(0,[z0,z1,z2,z4,z42,z6]),(0,[z0,z1,z2,z771,z6,z38])],[(0,[z0,z1,z959,z2,z4,z5]),(0,[z0,z1,z960,z2,z4,z6]),(0,[z0,z1,z961,z4,z5,z6]),(0,[z0,z1,z2,z4,z962,z6]),(0,[z0,z1,z30,z721,z2,z5])],[(0,[z0,z1,z2,z4,z5,z963]),(0,[z107,z0,z357,z2,z4,z5]),(0,[z0,z580,z2,z4,z5,z82]),(0,[z0,z1,z2,z151,z171,z6]),(0,[z0,z1,z172,z246,z5,z6])]],
   [[(0,[z1,z61,z2,z4,z5,z10]),(0,[z0,z1,z2,z964,z4,z5]),(0,[z144,z1,z2,z4,z60,z6]),(0,[z1,z2,z4,z65,z739,z6]),(0,[z0,z1,z2,z4,z5,z965]),(0,[z0,z1,z2,z487,z6,z38]),(0,[z0,z1,z2,z771,z4,z6])],[(0,[z0,z1,z966,z2,z4,z6]),(0,[z0,z1,z4,z715,z5,z6])],[(0,[z149,z429,z1,z2,z4,z5]),(0,[z59,z1,z2,z4,z739,z6]),(0,[z107,z0,z2,z4,z5,z709]),(0,[z0,z1,z777,z4,z5,z6]),(0,[z0,z1,z967,z4,z5,z6])],[(0,[z341,z1,z2,z32,z371,z6]),(0,[z64,z1,z2,z4,z739,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 568) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 568).take 394) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 962)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [568, 394] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 119).take 9).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [119, 9] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_44668

theorem PEqualNP.Outside.L_meta_44668 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276812992 * 2 ^ 32 + 4243105920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276812992 * 2 ^ 32 + 4243105920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_44668.solve