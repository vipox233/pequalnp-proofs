import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45868

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
  Nat.testBit (4008373472 * 2 ^ 32 + 4006127616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x208ac718621e1ad8#64 ++ 0x041158e30c43c35b#64 ++ 0xe99fcf18e63e3fff#64 ++ 0x7d33f9e31cc7c7ff#64 : BitVec 256),
   (0x0226117b08c2ee28#64 ++ 0x2044c22f61185dc5#64 ++ 0xf66633ff19c7fe3b#64 ++ 0xfeccc67fe338ffc7#64 : BitVec 256),
   (0x5858380dbe074740#64 ++ 0x8b0b0701b7c0e8e8#64 ++ 0xd8783c1ffe07c7c5#64 ++ 0xbb0f0783ffc0f8f8#64 : BitVec 256),
   (0x1d803ea01d6805b0#64 ++ 0x43b007d403ad00b6#64 ++ 0x7f803fe01ff807ff#64 ++ 0xeff007fc03ff00ff#64 : BitVec 256),
   (0x9f7d400017b5b001#64 ++ 0x13efa80002f6b600#64 ++ 0xbfffc0001ffff801#64 ++ 0xf7fff80003ffff00#64 : BitVec 256),
   (0xdff7afd6c0000002#64 ++ 0x1bfef5fad8000000#64 ++ 0xdfffffffe0000001#64 ++ 0xdbfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [13, 11]⟩, ⟨.and, [14, 9]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0002117b08424e28 0x2000422f610849c5 0x400033ff0000063a 0x0800067fe00000c7

def z1 : W := mkw 0x0008400002141000 0x0001080000428200 0xa99fc000063e3801 0x7533f80000c7c700

def z2 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0xf66633ff19c7fe3b 0xfeccc67fe338ffc7

def z3 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z4 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0xe99fcf18e63e3fff 0x7d33f9e31cc7c7ff

def z5 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z6 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0xdfffffffe0000001 0xdbfffffffc000000

def z7 : W := mkw 0x4058380daa074740 0x880b0701b540e8e8 0xc0783c1fe007c7c4 0x180f0783fc00f8f8

def z8 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0xbfffc0001ffff801 0xf7fff80003ffff00

def z9 : W := mkw 0x9ffd6e8017b5b001 0x13ffadd002f6b600 0xffffffe01ffff801 0xfffffffc03ffff00

def z10 : W := mkw 0x0080060000080090 0x001000c000010012 0x69800f00063807ff 0x6d3001e000c700ff

def z11 : W := mkw 0x3d8affb87f7e1ff8 0x47b15ff70fefc3ff 0xff9ffff8fffe3fff 0xfff3ffff1fffc7ff

def z12 : W := mkw 0x2002811860020a48 0x040050230c004149 0x00000018e0000000 0x000000031c000000

def z13 : W := mkw 0x058006a0016800b0 0x40b000d4002d0016 0x278003e001f8003a 0x44f0007c003f0007

def z14 : W := mkw 0x180038001c000500 0x03000700038000a0 0x58003c001e0007c5 0xab00078003c000f8

def z15 : W := mkw 0x1d00000015200000 0x03a0000002a40000 0x3f8000001ff80001 0xe7f0000003ff0000

def z16 : W := mkw 0xdff7afd6d5200002 0x1bfef5fadaa40000 0xfffffffffff80001 0xffffffffffff0000

def z17 : W := mkw 0x0000100908024600 0x00000201210048c0 0x000000001807c600 0x200000000300f8c0

def z18 : W := mkw 0x5850380dbc034740 0x8b0a0701b78068e8 0x50603c1ff801c7c4 0x8a0c0783ff0038f8

def z19 : W := mkw 0x0226015b0082ea08 0x2044c02b60105d41 0x8066001f0007f800 0x100cc003e000ff00

def z20 : W := mkw 0x5d5838adbf674760 0xcbab0715b7ece8ec 0xde783cffffc7c7c5 0xbbcf079ffff8f8f8

def z21 : W := mkw 0x5dd83e8dbe074740 0x8bbb07d1b7c0e8e8 0xdff83ffffe07c7c5 0xfbff07ffffc0f8f8

def z22 : W := mkw 0x00823ffb084a4fb8 0x601047ff610949f7 0x40003fff000007fe 0x080007ffe00000ff

def z23 : W := mkw 0x8725400001b0b001 0x10e4a80000361600 0xb7e7c00019fff801 0xf6fcf800033fff00

def z24 : W := mkw 0x000850291ff7fe29 0x20010a0523feffc5 0x200000001ffffe3a 0x2400000003ffffc7

def z25 : W := mkw 0x0224106308c0e420 0x2044820c61181c84 0xb66630e719c7f801 0xf6ccc61ce338ff00

def z26 : W := mkw 0x022410090882e600 0x0044820121105cc0 0xf666301f19c7fe01 0xfeccc603e338ffc0

def z27 : W := mkw 0x0080060000080090 0x001000c000010012 0x09800c00063801c4 0x0130018000c70038

def z28 : W := mkw 0x00801620084804b0 0x001002c401090096 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z29 : W := mkw 0x22aed77b6adefef8 0x2455daef6d5bdfdf 0xffffffffffffffff 0xffffffffffffffff

def z30 : W := mkw 0xdd59780dbf375741 0x9bab2f01b7e6eae8 0xd9f9fc1ffe3fc7c5 0xbb3f3f83ffc7f8f8

def z31 : W := mkw 0xdf778156c0000002 0x1beef02ad8000000 0x9fffc01fe0000001 0xd3fff803fc000000

def z32 : W := mkw 0x1d803e801c000500 0x03b007d0038000a0 0x5f803fe01e0007c5 0xebf007fc03c000f8

def z33 : W := mkw 0x208ad7197e1f5fd8 0x84115ae32fc3ebfb 0xe99fcf18fe3fffff 0x7d33f9e31fc7ffff

def z34 : W := mkw 0x0000000000080090 0x0000000000010012 0x20000000063807fe 0x2400000000c700ff

def z35 : W := mkw 0x2082bfb8684a0ff8 0x441057f70d0941ff 0x40003ff8e00007fe 0x080007ff1c0000ff

def z36 : W := mkw 0x208a8718620e0ad8 0x041150e30c41c15b 0xc8180f18e60607ff 0x390301e31cc0c0ff

def z37 : W := mkw 0x0226015b0082ea08 0x2044c02b60105d41 0xb666001f19c7f801 0xf6ccc003e338ff00

def z38 : W := mkw 0xdf7528c680000002 0x1beea518d0000000 0x166030e700000000 0x82cc061ce0000000

def z39 : W := mkw 0xdff7bff6dd6805b2 0x5bfef7fedbad00b6 0xfffffffffff807ff 0xffffffffffff00ff

def z40 : W := mkw 0x0000102008400420 0x0000020401080084 0x2000000019c0063a 0x24000000033800c7

def z41 : W := mkw 0x000010201d6805b0 0x4000020403ad00b6 0x200000001ff807fe 0x2400000003ff00ff

def z42 : W := mkw 0x022c40000294b000 0x0045880000529600 0xbfffc0001ffff801 0xf7fff80003ffff00

def z43 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0x967fc00019c7f800 0x92cff8000338ff00

def z44 : W := mkw 0xc2778156c0000002 0x184ef02ad8000000 0x807fc01fe0000000 0x100ff803fc000000

def z45 : W := mkw 0xc27d400da297f241 0x984fa801b452fe48 0x807fc01fe007f800 0x100ff803fc00ff00

def z46 : W := mkw 0x022400000080a000 0x0044800000101400 0x806600000007f800 0x100cc0000000ff00

def z47 : W := mkw 0x9d59400017351001 0x13ab280002e6a200 0x0999c00006380000 0x0133380000c70000

def z48 : W := mkw 0x9f7f517b1ff7fe29 0x33efea2f63feffc5 0xfffff3ff1ffffe3b 0xfffffe7fe3ffffc7

def z49 : W := mkw 0x5dd83eadbf6f47f0 0xcbbb07d5b7ede8fe 0xfff83fffffffc7ff 0xffff07fffffff8ff

def z50 : W := mkw 0x0082871040000000 0x001050e208000000 0xc99fcf18e0000001 0x5933f9e31c000000

def z51 : W := mkw 0xdfffefd6d7b5b003 0x1bfffdfadaf6b600 0xfffffffffffff801 0xffffffffffffff00

def z52 : W := mkw 0x0000102008400420 0x0000020401080084 0x760033e019c0063b 0xeec0067c033800c7

def z53 : W := mkw 0x180038091c024700 0x03000701238048e0 0xd8603c1f1e07c7c5 0xbb0c0783e3c0f8f8

def z54 : W := mkw 0x000000090082ea08 0x2000000120105d41 0x000000000007f800 0x000000000000ff00

def z55 : W := mkw 0x7afeff7ffedffff8 0xaf5fdfefffdbffff 0xffffffffffffffff 0xffffffffffffffff

def z56 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0x9078301ff807c000 0x920f0603ff00f800

def z57 : W := mkw 0x1d00000015200000 0x03a0000002a40000 0x0980000006380000 0x0130000000c70000

def z58 : W := mkw 0x2082c71040181898 0x041058e208030313 0x2187c3000038383a 0x4430f86000070707

def z59 : W := mkw 0x78daff1dfe1f5fd8 0x8f1b5fe3bfc3ebfb 0xf9ffff1ffe3fffff 0xff3fffe3ffc7ffff

def z60 : W := mkw 0x5858280db6074340 0x8b0b0501b6c0e868 0x88780c1fe607c1c4 0x110f0183fcc0f838

def z61 : W := mkw 0x9d51000000000000 0x13aa200000000000 0x0999c00000000000 0x0133380000000000

def z62 : W := mkw 0x3d8ac718773e1ad8 0x07b158e30ee7c35b 0xff9fcf18fffe3fff 0xfff3f9e31fffc7ff

def z63 : W := mkw 0x5d58380dbf274740 0x8bab0701b7e4e8e8 0xfff83c1fffffc7c5 0xffff0783fffff8f8

def z64 : W := mkw 0xbfffc718621e1ad8 0x17fff8e30c43c35b 0xffffcf18e63e3fff 0xfffff9e31cc7c7ff

def z65 : W := mkw 0xdff7bff6c8400422 0x1bfef7fed9080084 0xfffffffff9c0063b 0xffffffffff3800c7

def z66 : W := mkw 0x9f7d50091fb7f601 0x13efaa0123f6fec0 0xfffff01f1ffffe01 0xfffffe03e3ffffc0

def z67 : W := mkw 0x9f7d40000295b001 0x13efa8000052b600 0x9fffc0000007f801 0xd3fff8000000ff00

def z68 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0x260603e019c7fe3a 0x64c0c07c0338ffc7

def z69 : W := mkw 0x20084008221e1ad8 0x040108010443c35b 0xe8180c18e63e3fff 0x3d0301831cc7c7ff

def z70 : W := mkw 0x5ffe3fffbfefeff8 0xebffc7fff7fdfdff 0xfffe3fffffffffff 0xffffc7ffffffffff

def z71 : W := mkw 0x22a6c77240d8b8b8 0x2454d8ee481b1717 0x2787c3e001f8383a 0x44f0f87c003f0707

def z72 : W := mkw 0x1d802e8015280190 0x43b005d002a50032 0x3f800c001ff801c5 0xe7f0018003ff0038

def z73 : W := mkw 0x058016a01d6805b0 0x40b002d403ad00b6 0x278003e01ff807fe 0x64f0007c03ff00ff

def z74 : W := mkw 0x4000380da8024740 0x88000701b50048e8 0xd0603c1ff807c7c5 0xba0c0783ff00f8f8

def z75 : W := mkw 0x9dd96e80173d1191 0x53bb2dd002e7a232 0x0999cc00063801c4 0x0133398000c70038

def z76 : W := mkw 0x0008000822060240 0x000100010440c048 0xc8180c18e60607c5 0x390301831cc0c0f8

def z77 : W := mkw 0x9f75000000000000 0x13eea00000000000 0x1660000000000000 0x82cc000000000000

def z78 : W := mkw 0x1d883ea93f6f47f0 0xc3b107d527ede8fe 0x7f803fe01fffc7ff 0xeff007fc03fff8ff

def z79 : W := mkw 0x4002397fa8424f68 0xa800472ff50849ed 0x40003fffe00007fe 0x080007fffc0000ff

def z80 : W := mkw 0x022601520080a000 0x0044c02a40101400 0xf66633ff19c7f801 0xfeccc67fe338ff00

def z81 : W := mkw 0x0000000900024200 0x0000000120004840 0x8060001f0007c000 0x100c0003e000f800

def z82 : W := mkw 0x0226015200000000 0x0044c02a40000000 0xd66633ff00000001 0xdaccc67fe0000000

def z83 : W := mkw 0xddd1ae84c0000002 0x1bba35d098000000 0x0999cc00e0000000 0x013339801c000000

def z84 : W := mkw 0x1d00000000000000 0x03a0000000000000 0x1f80000000000001 0xc3f0000000000000

def z85 : W := mkw 0x4008380daa064740 0x88010701b540c8e8 0xc8183c1fe60607c5 0x39030783fcc0c0f8

def z86 : W := mkw 0x585038059c014500 0x8b0a0700b38028a0 0xd8783c1ff801c001 0x9b0f0783ff003800

def z87 : W := mkw 0x87a787d240000002 0x10f4f0fa48000000 0x0787c3e000000000 0x40f0f87c00000000

def z88 : W := mkw 0xdfffbfdffe074742 0x9bfff7fbffc0e8e8 0xdffffffffe07c7c5 0xfbffffffffc0f8f8

def z89 : W := mkw 0x022400000080a000 0x0044800000101400 0xb666000019c7f801 0xf6ccc0000338ff00

def z90 : W := mkw 0x9f7f415217b5b001 0x13efe82a42f6b600 0xfffff3ff1ffff801 0xfffffe7fe3ffff00

def z91 : W := mkw 0x0002811040000000 0x0000502208000000 0x801fc018e0000000 0x1003f8031c000000

def z92 : W := mkw 0x0008400822161240 0x000108010442c248 0xe99fcc18e63e3fc5 0x7d33f9831cc7c7f8

def z93 : W := mkw 0x0002117b08424e28 0x2000422f610849c5 0xd06033ff1807c63b 0xba0c067fe300f8c7

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0xa006000000063801 0x7400c0000000c700

def z95 : W := mkw 0xbddbc718773f1ad9 0x17bb78e30ee7e35b 0xe99fcf18e63e3fff 0x7d33f9e31cc7c7ff

def z96 : W := mkw 0x0008400017351001 0x0001080002e6a200 0x0000000006380000 0x0000000000c70000

def z97 : W := mkw 0x0000102908c2ee28 0x2000020521185dc5 0x2000000019c7fe3a 0x240000000338ffc7

def z98 : W := mkw 0x000010201d6805b0 0x4000020403ad00b6 0x760033e01ff807ff 0xeec0067c03ff00ff

def z99 : W := mkw 0x1d82af9040000000 0x03b055f208000000 0xdf9ffff8e0000001 0xdbf3ffff1c000000

def z100 : W := mkw 0xdf7d780dbfb7f741 0x9befaf01b7f6fee8 0xfffffc1fffffffc5 0xffffff83fffffff8

def z101 : W := mkw 0x9ffd7ea01ffdb5b1 0x53ffafd403ffb6b6 0xffffffe01fffffff 0xfffffffc03ffffff

def z102 : W := mkw 0x200ac118621e1ad8 0x040158230c43c35b 0xa01fc018e63e3ffe 0x3403f8031cc7c7ff

def z103 : W := mkw 0xffffff1dffbfffd9 0x9fffffe3bff7fffb 0xffffff1fffffffff 0xffffffe3ffffffff

def z104 : W := mkw 0xda7fb95ffe074742 0x9b4ff72bffc0e8e8 0xd87ffc1ffe07c7c5 0xbb0fff83ffc0f8f8

def z105 : W := mkw 0xa27fc1186297ba49 0x144ff8230c52f749 0x807fc018e007f800 0x100ff8031c00ff00

def z106 : W := mkw 0x1d58000017250000 0x03ab000002e4a000 0xbff800001fffc001 0xf7ff000003fff800

def z107 : W := mkw 0x1d802e8000000000 0x03b005d000000000 0x5f803fe000000001 0xcbf007fc00000000

def z108 : W := mkw 0xfdd9ee84e21c10d2 0x1fbb3dd09c43821a 0x0999cc00e63801c4 0x013339801cc70038

def z109 : W := mkw 0x9f75000000000000 0x13eea00000000000 0x9fffc00000000001 0xd3fff80000000000

def z110 : W := mkw 0x000810092a064640 0x000102012540c8c8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z111 : W := mkw 0x0226017200c0a828 0x2044c02e40181505 0x260603e001c0383a 0x44c0c07c00380707

def z112 : W := mkw 0x5a7e397fbec7ef68 0xab4fc72ff7d8fded 0xfe7e3fffffc7ffff 0xffcfc7fffff8ffff

def z113 : W := mkw 0x9f7d78001fb5b501 0x13efaf0003f6b6a0 0xfffffc001fffffc5 0xffffff8003fffff8

def z114 : W := mkw 0x20084008221e1ad8 0x040108010443c35b 0x20000000063e3ffe 0x2400000000c7c7ff

def z115 : W := mkw 0xffffefdee21e1ada 0x1ffffdfbdc43c35b 0xffffffffe63e3fff 0xfffffffffcc7c7ff

def z116 : W := mkw 0xdff7bfffc8c2ee2a 0x3bfef7fff9185dc5 0xfffffffff9c7fe3b 0xffffffffff38ffc7

def z117 : W := mkw 0x4082afd6c0000002 0x081055fad8000000 0x40003fffe0000000 0x080007fffc000000

def z118 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0x60000f18e63e3ffe 0x2c0001e31cc7c7ff

def z119 : W := mkw 0xdf7d400db7b7f241 0x9befa801b6f6fe48 0xbfffc01ffffff801 0xf7fff803ffffff00

def z120 : W := mkw 0xda7d780dbe97f741 0x9b4faf01b7d2fee8 0xd87ffc1ffe07ffc5 0xbb0fff83ffc0fff8

def z121 : W := mkw 0x000850093fb7f741 0x80010a0127f6fee8 0x200000001fffffc4 0x2400000003fffff8

def z122 : W := mkw 0xdff7bff7c8c0e422 0x3bfef7fef9181c84 0xdffffffff9c1c001 0xdbffffffff383800

def z123 : W := mkw 0x1d80060015280090 0x03b000c002a50012 0x7f800f001ff807ff 0xeff001e003ff00ff

def z124 : W := mkw 0x5858280ca2060240 0x0b0b05019440c048 0xd8783c1fe60607c5 0xbb0f0783fcc0c0f8

def z125 : W := mkw 0xdfffbffffec7ef6a 0xbbfff7ffffd8fded 0xffffffffffc7ffff 0xfffffffffff8ffff

def z126 : W := mkw 0x9f7d78a01ff5b521 0x53efaf1403feb6a4 0xbffff0e01ffff801 0xf7fffe1c03ffff00

def z127 : W := mkw 0x5a76397f9cc3ef28 0xab4ec72ff3987de5 0xf66633ff19c7fe3b 0xfeccc67fe338ffc7

def z128 : W := mkw 0x0226015200000000 0x0044c02a40000000 0x060603e000000000 0x40c0c07c00000000

def z129 : W := mkw 0x4058000da2074240 0x880b0001b440e848 0xc8780c1fe607c7c5 0x390f0183fcc0f8f8

def z130 : W := mkw 0x0226017b00c2ea28 0x2044c02f60185d45 0xa66603ff01c7f83a 0x54ccc07fe038ff07

def z131 : W := mkw 0x40803eada84a47f0 0xc81007d5b50948fe 0x40003fffe00007fe 0x080007fffc0000ff

def z132 : W := mkw 0x5850280480000000 0x0b0a050090000000 0xd8783c1fe0000001 0x9b0f0783fc000000

def z133 : W := mkw 0x872d400017b5b001 0x10e5a80002f6b600 0x2787c0001ffff800 0x64f0f80003ffff00

def z134 : W := mkw 0x5858780dbfb7f741 0x8b0b0f01b7f6fee8 0xf8783c1fffffffc5 0xbf0f0783fffffff8

def z135 : W := mkw 0x58582804b6050140 0x8b0b050096c0a028 0x08180c00e60001c4 0x010301801cc00038

def z136 : W := mkw 0x1d08400017341000 0x03a1080002e68200 0xbf9fc0001ffe3801 0xf7f3f80003ffc700

def z137 : W := mkw 0xbfffc71877bfbad9 0x17fff8e30ef7f75b 0xffffcf18ffffffff 0xfffff9e31fffffff

def z138 : W := mkw 0x4082afd6c0000002 0x081055fad8000000 0xc99fffffe0000001 0x5933fffffc000000

def z139 : W := mkw 0x9f75000015a1a001 0x13eea00002b43400 0x1660000019c1c000 0x82cc000003383800

def z140 : W := mkw 0x8725000000000000 0x10e4a00000000000 0x0787c00000000000 0x40f0f80000000000

def z141 : W := mkw 0x200850292adefef8 0x24010a05255bdfdf 0x200000001ffffffe 0x2400000003ffffff

def z142 : W := mkw 0x1d803ea91d6a47b0 0x43b007d523ad48f6 0xffe03fff1fffc7ff 0xfffc07ffe3fff8ff

def z143 : W := mkw 0x1a7c00001685a000 0x034f800002d0b400 0xbe7e00001fc7f801 0xf7cfc00003f8ff00

def z144 : W := mkw 0x008ac71042141000 0x001158e208428200 0xe99fcf18e63e3801 0x7d33f9e31cc7c700

def z145 : W := mkw 0xdff7bfdfc8024602 0x1bfef7fbf90048c0 0xdffffffff807c601 0xfbffffffff00f8c0

def z146 : W := mkw 0x00803ea0084805b0 0x401007d4010900b6 0x40003fe0000007fe 0x080007fc000000ff

def z147 : W := mkw 0x827d40000295b001 0x104fa8000052b600 0x807fc0000007f800 0x100ff8000000ff00

def z148 : W := mkw 0x1850000014010000 0x030a000002802000 0x106000001801c000 0x820c000003003800

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x2980000006380001 0x6530000000c70000

def z150 : W := mkw 0xdff7bff6c84805b2 0x5bfef7fed90900b6 0xdfffffffe00007ff 0xdbfffffffc0000ff

def z151 : W := mkw 0x0226117b1deaefb8 0x6044c22f63bd5df7 0xf66633ff1fffffff 0xfeccc67fe3ffffff

def z152 : W := mkw 0x0226117b08424e28 0x2044c22f610849c5 0xd66633ff0000063b 0xdaccc67fe00000c7

def z153 : W := mkw 0x000000000080a000 0x0000000000101400 0x2000000019c7f800 0x240000000338ff00

def z154 : W := mkw 0x1d802e8015280190 0x43b005d002a50032 0x09800c00063801c4 0x0130018000c70038

def z155 : W := mkw 0xdf7d6804b7b5b141 0x9befad0096f6b628 0xbfffcc00fffff9c5 0xf7fff9801fffff38

def z156 : W := mkw 0xdfffafd6f6050142 0x9bfff5fadec0a028 0xdfffffffe60001c5 0xdbfffffffcc00038

def z157 : W := mkw 0x20828718600a0ad8 0x041050e30c01415b 0x40000f18e00007fe 0x080001e31c0000ff

def z158 : W := mkw 0x5858280cb6070340 0x8b0b050196c0e068 0xc8180c18e60607c5 0x390301831cc0c0f8

def z159 : W := mkw 0xddd3afd6c0000002 0x1bba75fad8000000 0x4999ffffe0000000 0x09333ffffc000000

def z160 : W := mkw 0x258ac7b8637e1af8 0x44b158f70c6fc35f 0xef9fcff8e7fe3fff 0x7df3f9ff1cffc7ff

def z161 : W := mkw 0x4058000da2074240 0x880b0001b440e848 0x8078001fe007c000 0x100f0003fc00f800

def z162 : W := mkw 0x000810093e074740 0x8001020127c0e8e8 0x000000001e07c7c4 0x2000000003c0f8f8

def z163 : W := mkw 0x200ac11862161a48 0x040158230c42c349 0x801fc018e0063800 0x1003f8031c00c700

def z164 : W := mkw 0x200850283f7e1ff8 0x44010a0507efc3ff 0x200000001ffe3ffe 0x2400000003ffc7ff

def z165 : W := mkw 0x000850201ffdb5b1 0x40010a0403ffb6b6 0x200000001ffffffe 0x2400000003ffffff

def z166 : W := mkw 0x6082afdee00a0ada 0x0c1055fbdc01415b 0x40003fffe00007fe 0x080007fffc0000ff

def z167 : W := mkw 0xbf7fc11877b7ba49 0x17eff8230ef6f749 0xbfffc018fffff801 0xf7fff8031fffff00

def z168 : W := mkw 0x00880608220e02d0 0x001100c10441c05a 0xe9980f18e63e07ff 0x7d3301e31cc7c0ff

def z169 : W := mkw 0x022e517b0ad6fe28 0x2045ca2f615adfc5 0xfffff3ff1ffffe3b 0xfffffe7fe3ffffc7

def z170 : W := mkw 0xdf7d68c697b5b003 0x1befad18d2f6b600 0xbffff0e71ffff801 0xf7fffe1ce3ffff00

def z171 : W := mkw 0x0000102908c2ee28 0x2000020521185dc5 0xf060301f19c7fe3b 0xbe0c0603e338ffc7

def z172 : W := mkw 0x2088c600621c10d0 0x041118c00c43821a 0x0999cc00e63801c4 0x013339801cc70038

def z173 : W := mkw 0x1858000016050000 0x030b000002c0a000 0x987800001e07c001 0xb30f000003c0f800

def z174 : W := mkw 0x8725400001b0b001 0x10e4a80000361600 0x2787c00001f83800 0x44f0f800003f0700

def z175 : W := mkw 0x20084000221c10d0 0x040108000443821a 0x00000000063801c4 0x0000000000c70038

def z176 : W := mkw 0xdff7efd6c1b0b003 0x1bfefdfad8361600 0xffffffffe1f83801 0xdffffffffc3f0700

def z177 : W := mkw 0x20828718600a0ad8 0x041050e30c01415b 0xc99fcf18e00007ff 0x5933f9e31c0000ff

def z178 : W := mkw 0x000a411802161a08 0x000148230042c341 0xe99fc318063e3e3b 0x7d33f86300c7c7c7

def z179 : W := mkw 0xdfffbfffff6f47f2 0xdbfff7ffffede8fe 0xffffffffffffc7ff 0xfffffffffffff8ff

def z180 : W := mkw 0x0000000820020240 0x0000000104004048 0x40000c18e00007c4 0x080001831c0000f8

def z181 : W := mkw 0x00802e8000080190 0x401005d000010032 0x00000c00000001c4 0x0000018000000038

def z182 : W := mkw 0xdf77a9d6c0000002 0x1beef53ad8000000 0x967ff0ffe0000000 0x92cffe1ffc000000

def z183 : W := mkw 0x8059400002151001 0x100b28000042a200 0x0019c00000000000 0x0003380000000000

def z184 : W := mkw 0x0000100908024600 0x00000201210048c0 0xd060301f1807c601 0xba0c0603e300f8c0

def z185 : W := mkw 0xdff7bfffc8424e2a 0x3bfef7fff90849c5 0xdfffffffe000063b 0xdbfffffffc0000c7

def z186 : W := mkw 0x0000380008000500 0x00000700010000a0 0x40003c00000007c4 0x08000780000000f8

def z187 : W := mkw 0x9f7d000017a5a001 0x13efa00002f4b400 0x9e7800001fc7c001 0xb3cf000003f8f800

def z188 : W := mkw 0x180038201d6805b0 0x4300070403ad00b6 0x78003c001ff807ff 0xaf00078003ff00ff

def z189 : W := mkw 0xddd3af94c0000002 0x1bba75f298000000 0xc99fcf18e0000001 0x5933f9e31c000000

def z190 : W := mkw 0xddd1bea4dd6805b2 0x5bba37d49bad00b6 0x7f99ffe0fff807ff 0xeff33ffc1fff00ff

def z191 : W := mkw 0xdff7afd6c0080092 0x1bfef5fad8010012 0xffffffffe63807ff 0xfffffffffcc700ff

def z192 : W := mkw 0x0008400002141000 0x0001080000428200 0x801fc00000063800 0x1003f8000000c700

def z193 : W := mkw 0xbfffc71057bdb899 0x17fff8e20af7b713 0xbfffc3001ffff83b 0xf7fff86003ffff07

def z194 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0x56603fffe0000000 0x8acc07fffc000000

def z195 : W := mkw 0x180038001c000500 0x03000700038000a0 0x1000300018000000 0x8200060003000000

def z196 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0x106030071e07c7c4 0xa20c0600e3c0f8f8

def z197 : W := mkw 0x9fff7ffb1fffffb9 0x73ffefff63fffff7 0xffffffff1fffffff 0xffffffffe3ffffff

def z198 : W := mkw 0x0000000000000000 0x0000000000000000 0xc8180c18e0000001 0x190301831c000000

def z199 : W := mkw 0x4000380da8024740 0x88000701b50048e8 0x40003c1fe00007c4 0x08000783fc0000f8

def z200 : W := mkw 0xdfffefd6c295b003 0x1bfffdfad852b600 0xdfffffffe007f801 0xdbfffffffc00ff00

def z201 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0x566033ff19c1c63a 0x8acc067fe33838c7

def z202 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0x1ff9c0001ff9c000 0x83ff380003ff3800

def z203 : W := mkw 0x022400000080a000 0x0044800000101400 0x2606000001c03800 0x44c0c00000380700

def z204 : W := mkw 0x87a7c7d241b0b003 0x10f4f8fa48361600 0x2787c3e001f83800 0x44f0f87c003f0700

def z205 : W := mkw 0x9f75000015a1a001 0x13eea00002b43400 0xb666000019c7f801 0xf6ccc0000338ff00

def z206 : W := mkw 0x1d803e801d280590 0x43b007d003a500b2 0x59803c001e3807c5 0xab30078003c700f8

def z207 : W := mkw 0x0000102908424e28 0x20000205210849c5 0x000000000000063a 0x00000000000000c7

def z208 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0x89ffcc1fe0000000 0x113ff983fc000000

def z209 : W := mkw 0x5a7e395fbe87ef48 0xab4fc72bf7d0fde9 0xd87e3c1ffe07ffc5 0xbb0fc783ffc0fff8

def z210 : W := mkw 0x0008400017b5b001 0x0001080002f6b600 0xa99fc0001ffff801 0x7533f80003ffff00

def z211 : W := mkw 0x000a011822060a48 0x000140230440c149 0xe81e0f18e6063fff 0x7d03c1e31cc0c7ff

def z212 : W := mkw 0x050000a001600020 0x40a00014002c0004 0x060000e001c00000 0x00c0001c00380000

def z213 : W := mkw 0x585038059c014500 0x8b0a0700b38028a0 0x58603c071e01c7c5 0xab0c0780e3c038f8

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0xd060301f00000001 0x9a0c0603e0000000

def z215 : W := mkw 0x0082871040000000 0x001050e208000000 0x40000f18e0000000 0x080001e31c000000

def z216 : W := mkw 0xddd9be8dfe074742 0x9bbb37d1bfc0e8e8 0xd9f9fc1ffe07c7c5 0xbb3f3f83ffc0f8f8

def z217 : W := mkw 0x0226015a00020a08 0x0044c02b40004141 0xf66633ff00063e3b 0xfeccc67fe000c7c7

def z218 : W := mkw 0x4058100daa074640 0x880b0201b540e8c8 0xd078301ff807c601 0xba0f0603ff00f8c0

def z219 : W := mkw 0xdf7739ff88c2ee2a 0x3beee73ff1185dc5 0xf66633ff19c7fe3b 0xfeccc67fe338ffc7

def z220 : W := mkw 0x0224106308c0e420 0x2044820c61181c84 0x166030e719c1c000 0x82cc061ce3383800

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0x906000001807c001 0xb20c00000300f800

def z222 : W := mkw 0x1858000016050000 0x030b000002c0a000 0x0818000006000000 0x0103000000c00000

def z223 : W := mkw 0xffffffffeadefefa 0x3ffffffffd5bdfdf 0xffffffffffffffff 0xffffffffffffffff

def z224 : W := mkw 0x008006a0004800b0 0x401000d400090016 0x000003e00000003a 0x0000007c00000007

def z225 : W := mkw 0x585038059c014500 0x8b0a0700b38028a0 0x106030071801c000 0x820c0600e3003800

def z226 : W := mkw 0x9d59400017351001 0x13ab280002e6a200 0x3f99c0001ff80001 0xe7f3380003ff0000

def z227 : W := mkw 0x0008400002141000 0x0001080000428200 0x0999c00006380000 0x0133380000c70000

def z228 : W := mkw 0x9f7d50291ff7fe29 0x33efaa0523feffc5 0xbfffc0001ffffe3b 0xf7fff80003ffffc7

def z229 : W := mkw 0x0000102008400420 0x0000020401080084 0x400033e00000063a 0x0800067c000000c7

def z230 : W := mkw 0x9d59400017351001 0x13ab280002e6a200 0x99f9c0001e3fc001 0xb33f380003c7f800

def z231 : W := mkw 0x0226015b0082ea08 0x2044c02b60105d41 0xe066031f0007fe3b 0x7c0cc063e000ffc7

def z232 : W := mkw 0x8727517b09f2fe29 0x30e4ea2f613e5fc5 0xf7e7f3ff19fffe3b 0xfefcfe7fe33fffc7

def z233 : W := mkw 0x1fa43ee31de8e5b0 0x63f487dc63bd1cb6 0x7fe03fe71ff9c7ff 0xeffc07fce3ff38ff

def z234 : W := mkw 0x208ac710621c18d8 0x041158e20c43831b 0x299fcf00e63839fe 0x4533f9e01cc7073f

def z235 : W := mkw 0x427e015fa287ea48 0xa84fc02bf450fd49 0x807e001fe007f800 0x100fc003fc00ff00

def z236 : W := mkw 0x9f7500000080a000 0x13eea00000101400 0xbfffc00019c7f801 0xf7fff8000338ff00

def z237 : W := mkw 0x0002011800020a08 0x0000402300004141 0x400003180000063a 0x08000063000000c7

def z238 : W := mkw 0x180038201c400520 0x03000704038800a4 0x7e003fe01fc007ff 0xefc007fc03f800ff

def z239 : W := mkw 0x9f7f417217f5b829 0x33efe82e42feb705 0xbfffc3e01ffff83b 0xf7fff87c03ffff07

def z240 : W := mkw 0x0002017200400828 0x2000402e40080105 0x000003e00000003a 0x0000007c00000007

def z241 : W := mkw 0x9dd97ea01f7d15b1 0x53bb2fd403efa2b6 0x7f99ffe01ff807ff 0xeff33ffc03ff00ff

def z242 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x29800c001ff807fe 0x2530018003ff00ff

def z243 : W := mkw 0xdff7bfd6dc000502 0x1bfef7fadb8000a0 0xdffffffffe0007c5 0xfbffffffffc000f8

def z244 : W := mkw 0xdf7d38cfbe074742 0x9befa719f7c0e8e8 0xde783cfffe07c7c5 0xbbcf079fffc0f8f8

def z245 : W := mkw 0x4082bfdfe8024742 0x881057fbfd0048e8 0x40003fffe00007c4 0x080007fffc0000f8

def z246 : W := mkw 0xbfffd77b7ffffef9 0x37fffaef6fffffdf 0xffffffffffffffff 0xffffffffffffffff

def z247 : W := mkw 0xdf7528c680000002 0x1beea518d0000000 0xde783cffe0000001 0x9bcf079ffc000000

def z248 : W := mkw 0x2080c60040181090 0x041018c008030212 0x0181c00000380000 0x0030380000070000

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x48000c00060007c5 0x2900018000c000f8

def z250 : W := mkw 0x58dabf1dfe074740 0x8b1b57e3bfc0e8e8 0xd9ffff1ffe07c7c5 0xfb3fffe3ffc0f8f8

def z251 : W := mkw 0x0226017200c0a828 0x2044c02e40181505 0xf66633ff01c0383b 0xdeccc67fe0380707

def z252 : W := mkw 0x9fffc7d257b5b003 0x13fff8fa4af6b600 0xbfffc3e01ffff801 0xf7fff87c03ffff00

def z253 : W := mkw 0x185810093e074740 0x830b020127c0e8e8 0x987800001e07c7c5 0xb30f000003c0f8f8

def z254 : W := mkw 0xc0518004c0000002 0x180a300098000000 0x0019c000e0000000 0x000338001c000000

def z255 : W := mkw 0x9f7510631de1e421 0x33eea20c63bc3c84 0x166030e719c1c000 0x82cc061ce3383800

def z256 : W := mkw 0x208ad7396adefef8 0x24115ae72d5bdfdf 0xe99fcf18ffffffff 0x7d33f9e31fffffff

def z257 : W := mkw 0x9f7d400017351001 0x13efa80002e6a200 0x9fffc00006380001 0xd3fff80000c70000

def z258 : W := mkw 0x8581868040000002 0x10b030d008000000 0x0181c00000000000 0x0030380000000000

def z259 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0x17e7f3e700000000 0xc2fcfe7ce0000000

def z260 : W := mkw 0x1858400016151000 0x030b080002c2a200 0xb9ffc0001e3ff801 0xf73ff80003c7ff00

def z261 : W := mkw 0x0000400000101000 0x0000080000020200 0x2187c00000383800 0x4430f80000070700

def z262 : W := mkw 0x022601180082aa08 0x0044c02300105541 0xf666031819c7fe3b 0xfeccc0630338ffc7

def z263 : W := mkw 0x222ed17b6ad6fe68 0x2445da2f6d5adfcd 0xf67ff3fff9c7fe3b 0xfecffe7fff38ffc7

def z264 : W := mkw 0xdfffafdfe2074242 0x9bfff5fbfc40e848 0xdfffffffe007c001 0xdbfffffffc00f800

def z265 : W := mkw 0xddd1ae84d5280192 0x5bba35d09aa50032 0x0999cc00e63801c4 0x013339801cc70038

def z266 : W := mkw 0x7858780dbe1f5fd8 0x8f0b0f01b7c3ebfb 0xf8783c1ffe3fffff 0xbf0f0783ffc7ffff

def z267 : W := mkw 0x008a871862060240 0x001150e30c40c048 0xc99fcf18e60607c5 0x7933f9e31cc0c0f8

def z268 : W := mkw 0x0008000022040040 0x0001000004408008 0x08180c00e60001c4 0x010301801cc00038

def z269 : W := mkw 0x9fa7afd240000002 0x13f4f5fa48000000 0x5f87ffe000000001 0xcbf0fffc00000000

def z270 : W := mkw 0x200850093e1f5fd8 0x84010a0127c3ebfb 0x200000001e3ffffe 0x2400000003c7ffff

def z271 : W := mkw 0x0224000000000000 0x0044800000000000 0x9666000000000001 0xd2ccc00000000000

def z272 : W := mkw 0x058006a0016800b0 0x40b000d4002d0016 0x6f800fe007f807ff 0x6df001fc00ff00ff

def z273 : W := mkw 0x0000000800020a08 0x0000000100004141 0x2000000000063e3a 0x240000000000c7c7

def z274 : W := mkw 0x0224004200000000 0x0044800840000000 0x166030e700000000 0x82cc061ce0000000

def z275 : W := mkw 0xc275004680000002 0x184ea008d0000000 0x0060000700000000 0x000c0000e0000000

def z276 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x378033e019f8003a 0xc6f0067c033f0007

def z277 : W := mkw 0xc2778156c0000002 0x184ef02ad8000000 0xd67ff3ffe0000001 0xdacffe7ffc000000

def z278 : W := mkw 0x8727417201f0b829 0x30e4e82e403e1705 0x2787c3e001f8383a 0x44f0f87c003f0707

def z279 : W := mkw 0xa7a7c7d24018189a 0x14f4f8fa48030313 0x2787c3e00038383a 0x44f0f87c00070707

def z280 : W := mkw 0x0000100928024740 0x80000201250048e8 0x00000000000007c4 0x00000000000000f8

def z281 : W := mkw 0x20000008200a0ad8 0x040000010401415b 0x00000000000007fe 0x00000000000000ff

def z282 : W := mkw 0xdf7538c79c014502 0x9beea718f38028a0 0x166030e71801c000 0x82cc061ce3003800

def z283 : W := mkw 0x1fa63ffb1deaefb8 0x63f4c7ff63bd5df7 0xffe63fff1fffffff 0xfffcc7ffe3ffffff

def z284 : W := mkw 0x827500000081a001 0x104ea00000103400 0x006000000001c000 0x000c000000003800

def z285 : W := mkw 0x1f2639fb1de2ef28 0x63e4c73f63bc5de5 0xf66633ff19c7fe3b 0xfeccc67fe338ffc7

def z286 : W := mkw 0x9ff53ea01d6805b0 0x53fea7d403ad00b6 0xffffffe01ff807ff 0xfffffffc03ff00ff

def z287 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0x89ffc000063ff800 0x113ff80000c7ff00

def z288 : W := mkw 0xdff7afd6c080a002 0x1bfef5fad8101400 0xfffffffff9c7f801 0xffffffffff38ff00

def z289 : W := mkw 0xc277815fc082ea0a 0x384ef02bf8105d41 0x807fc01fe007f800 0x100ff803fc00ff00

def z290 : W := mkw 0x4050000580014000 0x880a0000b0002800 0x006000070001c000 0x000c0000e0003800

def z291 : W := mkw 0x222e517b2adefef8 0x2445ca2f655bdfdf 0xf66633ff1fffffff 0xfeccc67fe3ffffff

def z292 : W := mkw 0x1858400017b5b001 0x030b080002f6b600 0xb87800001ffff801 0xb70f000003ffff00

def z293 : W := mkw 0x022400430080e000 0x2044800860101c00 0x006000070001c000 0x000c0000e0003800

def z294 : W := mkw 0x058016a0096804b0 0x40b002d4012d0096 0x778033e019f8063b 0xeef0067c033f00c7

def z295 : W := mkw 0x9f7d400837b7b241 0x13efa80106f6f648 0xffffcc18ffffffc5 0xfffff9831ffffff8

def z296 : W := mkw 0xdff7bfffddeaefba 0x7bfef7fffbbd5df7 0xffffffffffffffff 0xffffffffffffffff

def z297 : W := mkw 0x222ec15b6296fa48 0x2445d82b6c52df49 0x807fc01fe007f800 0x100ff803fc00ff00

def z298 : W := mkw 0x1d883ea83f6e07f0 0x43b107d507edc0fe 0xff983ff8fffe07ff 0xfff307ff1fffc0ff

def z299 : W := mkw 0x38dac718761f1ad8 0x071b58e30ec3e35b 0xf9ffcf18fe3fffff 0xff3ff9e31fc7ffff

def z300 : W := mkw 0x4000280480000000 0x0800050090000000 0x40003c1fe0000000 0x08000783fc000000

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0x560033e000000001 0xcac0067c00000000

def z302 : W := mkw 0x1d0038a01d600520 0x43a0071403ac00a4 0x160030e019c00000 0x82c0061c03380000

def z303 : W := mkw 0x9f7538a01de1a521 0x53eea71403bc34a4 0x166030e019c1c000 0x82cc061c03383800

def z304 : W := mkw 0x5dd02e8480000000 0x0bba05d090000000 0xdff83fffe0000001 0xdbff07fffc000000

def z305 : W := mkw 0x5d803eadbd6a47f0 0xcbb007d5b7ad48fe 0x7f803ffffff807ff 0xeff007ffffff00ff

def z306 : W := mkw 0x0000002000c0a828 0x2000000400181505 0x2000000001c0383a 0x0400000000380707

def z307 : W := mkw 0x00802e8000000000 0x001005d000000000 0x40003fe000000000 0x080007fc00000000

def z308 : W := mkw 0x1858000836070240 0x030b000106c0e048 0xd8780c18fe07c7c5 0xbb0f01831fc0f8f8

def z309 : W := mkw 0xe27fc15ee2161a4a 0x1c4ff82bdc42c349 0x807fc01fe0063800 0x100ff803fc00c700

def z310 : W := mkw 0x1d803ea01d600520 0x43b007d403ac00a4 0x5f803fe019c00001 0xcbf007fc03380000

def z311 : W := mkw 0x00001020084805b0 0x40000204010900b6 0x00000000000007fe 0x00000000000000ff

def z312 : W := mkw 0x1fa62fd200000000 0x03f4c5fa40000000 0xdfe63fff00000001 0xdbfcc7ffe0000000

def z313 : W := mkw 0x2088c600621c10d0 0x041118c00c43821a 0xa99fcc00e63e39c5 0x7533f9801cc7c738

def z314 : W := mkw 0x02a6177b08caeeb8 0x2054c2ef61195dd7 0xffe63fff1fffffff 0xfffcc7ffe3ffffff

def z315 : W := mkw 0x9ffd460017bdb091 0x13ffa8c002f7b612 0xffffcf001fffffff 0xfffff9e003ffffff

def z316 : W := mkw 0xdffffff6dffdb5b3 0x5bfffffedbffb6b6 0xffffffffffffffff 0xffffffffffffffff

def z317 : W := mkw 0x5800380dbc024740 0x8b000701b78048e8 0x58003c1ffe0007c5 0xab000783ffc000f8

def z318 : W := mkw 0x9ff53ea01de9a5b1 0x53fea7d403bd34b6 0x7fe03fe01ff9c7ff 0xeffc07fc03ff38ff

def z319 : W := mkw 0x5850380d88024600 0x0b0a0701b10048c0 0xd8783c1ff807c601 0xbb0f0783ff00f8c0

def z320 : W := mkw 0xfff7afdee00a0ada 0x1ffef5fbdc01415b 0xdfffffffe00007ff 0xdbfffffffc0000ff

def z321 : W := mkw 0x87a546a001f8b0b1 0x50f4a8d4003f1616 0x2787c3e001f8383a 0x44f0f87c003f0707

def z322 : W := mkw 0xfff7efd6c018189a 0x1ffefdfad8030313 0xffffffffe038383b 0xdffffffffc070707

def z323 : W := mkw 0x008016201d6805b0 0x401002c403ad00b6 0x69800f001ff807ff 0x6d3001e003ff00ff

def z324 : W := mkw 0x1d0038001d200500 0x03a0070003a400a0 0x7f803c001ff807c5 0xeff0078003ff00f8

def z325 : W := mkw 0x5858382dbe474760 0x8b0b0705b7c8e8ec 0xfe783fffffc7c7ff 0xffcf07fffff8f8ff

def z326 : W := mkw 0x58583805be054540 0x8b0b0700b7c0a8a8 0x18783c07fe01c1c4 0x830f0780ffc03838

def z327 : W := mkw 0x5a7c386fbec7e760 0xab4f870df7d8fcec 0xde783cffffc7c7c5 0xbbcf079ffff8f8f8

def z328 : W := mkw 0x40002804a0000140 0x8800050094000028 0x00000c00e00001c4 0x000001801c000038

def z329 : W := mkw 0x0080060000080090 0x001000c000010012 0x218003000038003a 0x4430006000070007

def z330 : W := mkw 0x78d8ee04f61d11d0 0x8f1b1dc09ec3a23a 0x0999cc00e63801c4 0x013339801cc70038

def z331 : W := mkw 0xdf7528c680000002 0x1beea518d0000000 0x9ffff0e700000001 0xd3fffe1ce0000000

def z332 : W := mkw 0x0000000015a1a001 0x0000000002b43400 0x0000000019c1c000 0x0000000003383800

def z333 : W := mkw 0x5850380da8024740 0x8b0a0701b50048e8 0xd8783c1fe00007c5 0x9b0f0783fc0000f8

def z334 : W := mkw 0xdff7aff6c0c0a82a 0x3bfef5fed8181505 0xffffffffe1c0383b 0xdffffffffc380707

def z335 : W := mkw 0x40028156c0000002 0x0800502ad8000000 0x0000001fe0000000 0x00000003fc000000

def z336 : W := mkw 0x9ffd46a017fdb0b1 0x53ffa8d402ffb616 0xbfffc3e01ffff83b 0xf7fff87c03ffff07

def z337 : W := mkw 0x05803ea0096805b0 0x40b007d4012d00b6 0x67803fe001f807fe 0x4cf007fc003f00ff

def z338 : W := mkw 0x1f2438e31de0e520 0x63e4871c63bc1ca4 0x166030e719c1c000 0x82cc061ce3383800

def z339 : W := mkw 0x9f75000015a1a001 0x13eea00002b43400 0x3fe000001ff9c001 0xe7fc000003ff3800

def z340 : W := mkw 0x605ac11de2175a48 0x8c0b5823bc42eb49 0x807fc01fe007f800 0x100ff803fc00ff00

def z341 : W := mkw 0x6082bf1de80a4fd8 0x8c1057e3bd0149fb 0x40003f1fe00007fe 0x080007e3fc0000ff

def z342 : W := mkw 0x5dd82e84b72d01d0 0xcbbb05d096e5a03a 0x09980c00e63801c4 0x013301801cc70038

def z343 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0xc01fcf18e0063ffe 0x1803f9e31c00c7ff

def z344 : W := mkw 0x1d802e8015200000 0x03b005d002a40000 0x7f803fe01ff80001 0xeff007fc03ff0000

def z345 : W := mkw 0x22aec75a621e1ad8 0x0455d8eb4c43c35b 0xffffffffe63e3fff 0xfffffffffcc7c7ff

def z346 : W := mkw 0xe2ffc75ee21e1ada 0x1c5ff8ebdc43c35b 0xe9ffcf1fe63e3fff 0x7d3ff9e3fcc7c7ff

def z347 : W := mkw 0x5dd03ea49d6805b0 0x4bba07d493ad00b6 0xfff83ffffff807ff 0xffff07ffffff00ff

def z348 : W := mkw 0x208ac71877bfbad9 0x041158e30ef7f75b 0xe99fcf18ffffffff 0x7d33f9e31fffffff

def z349 : W := mkw 0x827d40000295b001 0x104fa8000052b600 0xb67fc00019c7f801 0xf6cff8000338ff00

def z350 : W := mkw 0xdff7afdec0020a0a 0x1bfef5fbd8004141 0xffffffffe0063e3b 0xfffffffffc00c7c7

def z351 : W := mkw 0x1d0038a01d600520 0x43a0071403ac00a4 0x760033e019c0063b 0xeec0067c033800c7

def z352 : W := mkw 0x0000000000000000 0x0000000000000000 0x3600000019c00001 0xe6c0000003380000

def z353 : W := mkw 0xdfffffffdff7fe2b 0x3bfffffffbfeffc5 0xfffffffffffffe3b 0xffffffffffffffc7

def z354 : W := mkw 0x5858280da2074240 0x8b0b0501b440e848 0xd8783c1fe007c001 0x9b0f0783fc00f800

def z355 : W := mkw 0x0008400017b5b001 0x0001080002f6b600 0x200000001ffff800 0x2400000003ffff00

def z356 : W := mkw 0x0002011800020a08 0x0000402300004141 0xe006031800063e3b 0x7c00c0630000c7c7

def z357 : W := mkw 0x180838083e060740 0x0301070107c0c0e8 0xd8183c18fe0607c5 0xbb0307831fc0c0f8

def z358 : W := mkw 0x22aec77a62debaf8 0x2455d8ef4c5bd75f 0xef9fcff8e7fe3fff 0x7df3f9ff1cffc7ff

def z359 : W := mkw 0x1d00288000000000 0x03a0051000000000 0x160030e000000000 0x82c0061c00000000

def z360 : W := mkw 0x200ac11862161a48 0x040158230c42c349 0xc81fcc18e6063fc5 0x3903f9831cc0c7f8

def z361 : W := mkw 0x000840000295b001 0x000108000052b600 0x000000000007f800 0x000000000000ff00

def z362 : W := mkw 0x1d82bfb05d6805b0 0x43b057f60bad00b6 0xff9ffff8fff807ff 0xfff3ffff1fff00ff

def z363 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0xa19fc318e03e383a 0x5433f8631c07c707

def z364 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x56003fe019c007fe 0x8ac007fc033800ff

def z365 : W := mkw 0x5a7e395fbe074740 0x8b4fc72bf7c0e8e8 0xde7e3ffffe07c7c5 0xfbcfc7ffffc0f8f8

def z366 : W := mkw 0x00803ea0084805b0 0x401007d4010900b6 0x69803fe0063807ff 0x6d3007fc00c700ff

def z367 : W := mkw 0x185838001e050500 0x030b070003c0a0a0 0xd8783c001e07c7c5 0xbb0f078003c0f8f8

def z368 : W := mkw 0x8275000000000000 0x104ea00000000000 0x807fc00000000000 0x100ff80000000000

def z369 : W := mkw 0x5dd03ea59d6945b0 0xcbba07d4b3ad28b6 0x7fe03fe71ff9c7ff 0xeffc07fce3ff38ff

def z370 : W := mkw 0x1a26397b1cc2ef28 0x2344c72f63985de5 0xfe663fff1fc7ffff 0xffccc7ffe3f8ffff

def z371 : W := mkw 0x22a6977b68caeef8 0x2454d2ef6d195ddf 0xf6663ffff9c7ffff 0xfeccc7ffff38ffff

def z372 : W := mkw 0x22a6d77b48dafeb8 0x2454daef691b5fd7 0xf7e7f3ff19fffe3b 0xfefcfe7fe33fffc7

def z373 : W := mkw 0x3d887ea83f7e1ff8 0x47b10fd507efc3ff 0x7f803fe01ffe3fff 0xeff007fc03ffc7ff

def z374 : W := mkw 0x78daef1ce21e1ad8 0x0f1b5de39c43c35b 0xf9ffff1fe63e3fff 0xff3fffe3fcc7c7ff

def z375 : W := mkw 0xddd1ae84c0000002 0x1bba35d098000000 0x5f99ffe0e0000001 0xcbf33ffc1c000000

def z376 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0x966630ff19c7f800 0x92ccc61fe338ff00

def z377 : W := mkw 0x180838093e074740 0x8301070127c0e8e8 0x58003c001e07c7c5 0xab00078003c0f8f8

def z378 : W := mkw 0x200ac11862161a48 0x040158230c42c349 0xa99fc018e63e3801 0x7533f8031cc7c700

def z379 : W := mkw 0x1a7e117b1ec7ee28 0x234fc22f63d8fdc5 0xfe7e33ff1fc7fe3b 0xffcfc67fe3f8ffc7

def z380 : W := mkw 0x60dac71de21f5ad8 0x8c1b58e3bc43eb5b 0xe9ffcf1fe63fffff 0x7d3ff9e3fcc7ffff

def z381 : W := mkw 0x0008000016050000 0x0001000002c0a000 0x000000001e07c000 0x2000000003c0f800

def z382 : W := mkw 0x1fa63ff21de8adb8 0x63f4c7fe43bd15b7 0x7f863fe01ff83fff 0xeff0c7fc03ff07ff

def z383 : W := mkw 0xdff7afdfc082ea0a 0x3bfef5fbf8105d41 0xdfffffffe007f801 0xdbfffffffc00ff00

def z384 : W := mkw 0x1800000014000000 0x0300000002800000 0x180000001e000001 0xa300000003c00000

def z385 : W := mkw 0x022e117b2ac6ee68 0x2045c22f6558ddcd 0xfe7e3fffffc7ffff 0xffcfc7fffff8ffff

def z386 : W := mkw 0xdff7afd6d5a1a003 0x1bfef5fadab43400 0xdffffffff9c1c001 0xdbffffffff383800

def z387 : W := mkw 0x4226397fa8c2ef68 0xa844c72ff5185ded 0xf6663ffff9c7ffff 0xfeccc7ffff38ffff

def z388 : W := mkw 0x9f77117b1de3ee29 0x33eee22f63bc7dc5 0xf66633ff19c7fe3b 0xfeccc67fe338ffc7

def z389 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0x899fcc18e63e39c4 0x1133f9831cc7c738

def z390 : W := mkw 0xdffdee84d7b5b003 0x1bffbdd09af6b600 0xbfffcc00fffff801 0xf7fff9801fffff00

def z391 : W := mkw 0xdff52ec680000002 0x1bfea5d8d0000000 0x5fe03fe700000001 0xcbfc07fce0000000

def z392 : W := mkw 0x4000000da0024240 0x88000001b4004848 0x0000001fe0000000 0x00000003fc000000

def z393 : W := mkw 0x2082c71040181898 0x041058e208030313 0xe99fcf18e038383b 0x5d33f9e31c070707

def z394 : W := mkw 0x1d887ea01ffdb5b1 0x43b10fd403ffb6b6 0x7f803fe01fffffff 0xeff007fc03ffffff

def z395 : W := mkw 0x7ddaffbdff7f5ff8 0xcfbb5ff7bfefebff 0xffffffffffffffff 0xffffffffffffffff

def z396 : W := mkw 0xdf7f797fbff7ff69 0xbbefef2ff7feffed 0xffffffffffffffff 0xffffffffffffffff

def z397 : W := mkw 0x1dd83ea01f6d05b0 0x43bb07d403eda0b6 0xfff83fe01fffc7ff 0xffff07fc03fff8ff

def z398 : W := mkw 0x2082977b684a4ef8 0x241052ef6d0949df 0x40003fffe00007fe 0x080007fffc0000ff

def z399 : W := mkw 0x0000000000000000 0x0000000000000000 0x899fc00000000001 0x5133f80000000000

def z400 : W := mkw 0x3d82ffb05d781db8 0x47b05ff60baf03b7 0x7f87ffe01ff83fff 0xeff0fffc03ff07ff

def z401 : W := mkw 0x9f75000015200000 0x13eea00002a40000 0xbfffc0001ff80001 0xf7fff80003ff0000

def z402 : W := mkw 0x9ff787d240000002 0x13fef0fa48000000 0x9fffc3e000000001 0xd3fff87c00000000

def z403 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x49803fe0063807fe 0x093007fc00c700ff

def z404 : W := mkw 0x07a617fb09eaeeb8 0x60f4c2ff613d5dd7 0xf7e633ff19fffe3b 0xfefcc67fe33fffc7

def z405 : W := mkw 0x2008400837bfbad9 0x0401080106f7f75b 0x200000001ffffffe 0x2400000003ffffff

def z406 : W := mkw 0x0002011800020a08 0x0000402300004141 0x8006001800063800 0x1000c0030000c700

def z407 : W := mkw 0x1800280014000100 0x0300050002800020 0x08000c00060001c4 0x0100018000c00038

def z408 : W := mkw 0x0082871040000000 0x001050e208000000 0x0187c30000000000 0x4030f86000000000

def z409 : W := mkw 0x4000380588004500 0x88000700b10008a0 0x0000300700000000 0x00000600e0000000

def z410 : W := mkw 0x9f77117b08c2ee28 0x33eee22f61185dc5 0xfffff3ff19c7fe3b 0xfffffe7fe338ffc7

def z411 : W := mkw 0xddd9ae84f6050142 0x9bbb35d09ec0a028 0x0999cc00e60001c4 0x013339801cc00038

def z412 : W := mkw 0x0224102908c2ee28 0x2044820521185dc5 0xb666000019c7fe3b 0xf6ccc0000338ffc7

def z413 : W := mkw 0x388aff187e1e1fd8 0x07115fe30fc3c3fb 0xf99fff18fe3e3fff 0xff33ffe31fc7c7ff

def z414 : W := mkw 0x5858780dbe175740 0x8b0b0f01b7c2eae8 0xf9fffc1ffe3fffc5 0xff3fff83ffc7fff8

def z415 : W := mkw 0x0224106b08c2ee28 0x2044820d61185dc5 0x366030e719c7fe3a 0xa6cc061ce338ffc7

def z416 : W := mkw 0x5d82bff6dd6805b2 0x4bb057fedbad00b6 0x7f803ffffff807ff 0xeff007ffffff00ff

def z417 : W := mkw 0x0002111908024e08 0x00004223210049c1 0xf066331f1807fe3b 0xfe0cc663e300ffc7

def z418 : W := mkw 0x822540000090b001 0x1044a80000121600 0x0007c00000003800 0x0000f80000000700

def z419 : W := mkw 0xdf75280480000000 0x1beea50090000000 0xdffffc1fe0000001 0xdbffff83fc000000

def z420 : W := mkw 0x000810093e074740 0x8001020127c0e8e8 0xc8180c18fe07c7c5 0x390301831fc0f8f8

def z421 : W := mkw 0xddd9ee84d7351003 0x1bbb3dd09ae6a200 0x0999cc00e6380000 0x013339801cc70000

def z422 : W := mkw 0x42a6afd6c0000002 0x0854d5fad8000000 0xd6663fffe0000001 0xdaccc7fffc000000

def z423 : W := mkw 0x87a787f2416800b2 0x50f4f0fe482d0016 0x2787c3e001f8003a 0x44f0f87c003f0007

def z424 : W := mkw 0xdffd7eadbffff7f1 0xdbffafd5b7fffefe 0xffffffffffffffff 0xffffffffffffffff

def z425 : W := mkw 0xa2ffc718629fbad9 0x145ff8e30c53f75b 0xe9ffcf18e63fffff 0x7d3ff9e31cc7ffff

def z426 : W := mkw 0x5850280480000000 0x0b0a050090000000 0x1060300700000000 0x820c0600e0000000

def z427 : W := mkw 0x1d0010201d6805b0 0x43a0020403ad00b6 0x3f8000001ff807ff 0xe7f0000003ff00ff

def z428 : W := mkw 0xffffefd6e21c10d2 0x1ffffdfadc43821a 0xdfffffffe63801c5 0xdbfffffffcc70038

def z429 : W := mkw 0x78daef1cf61f1bd8 0x8f1b5de39ec3e37b 0xe99fcf18e63e3fff 0x7d33f9e31cc7c7ff

def z430 : W := mkw 0x0224102008c0a420 0x0044820401181484 0xf66633e019c7fe3b 0xfeccc67c0338ffc7

def z431 : W := mkw 0x1f26117b1de2ee28 0x23e4c22f63bc5dc5 0xffe633ff1ffffe3b 0xfffcc67fe3ffffc7

def z432 : W := mkw 0x0000102908c2ee28 0x2000020521185dc5 0x760033e019c7fe3b 0xeec0067c0338ffc7

def z433 : W := mkw 0x1d802e8000080090 0x03b005d000010012 0x7f803fe0063807ff 0xeff007fc00c700ff

def z434 : W := mkw 0x000810093e074740 0x8001020127c0e8e8 0xd060301f1e07c7c5 0xba0c0603e3c0f8f8

def z435 : W := mkw 0x1d802e8015280190 0x43b005d002a50032 0x5f803fe0063801c5 0xcbf007fc00c70038

def z436 : W := mkw 0x0000400001b0b001 0x0000080000361600 0x2000000001f83800 0x04000000003f0700

def z437 : W := mkw 0x0580068001280090 0x40b000d000250012 0x0180000000380000 0x0030000000070000

def z438 : W := mkw 0x0226017200c0a828 0x2044c02e40181505 0xb66603e019c7f83b 0xf6ccc07c0338ff07

def z439 : W := mkw 0x1d8006a0156800b0 0x43b000d402ad0016 0x3f8003e01ff8003b 0xe7f0007c03ff0007

def z440 : W := mkw 0x9d59400017b5b001 0x13ab280002f6b600 0x2999c0001ffff800 0x2533380003ffff00

def z441 : W := mkw 0x0226115b0882ee08 0x2044c22b61105dc1 0xd066301f1807fe01 0xba0cc603e300ffc0

def z442 : W := mkw 0x000810293f6f47f0 0xc001020527ede8fe 0x200000001fffc7fe 0x2400000003fff8ff

def z443 : W := mkw 0x0082871040080090 0x001050e208010012 0xe99fcf18e63807ff 0x7d33f9e31cc700ff

def z444 : W := mkw 0xdfffafdee2060242 0x1bfff5fbdc40c048 0xdfffffffe60607c5 0xfbfffffffcc0c0f8

def z445 : W := mkw 0x2082871040080898 0x041050e208010113 0x000003000000003a 0x0000006000000007

def z446 : W := mkw 0x58dabfdffe074742 0x8b1b57fbffc0e8e8 0xd8783ffffe07c7c5 0xbb0f07ffffc0f8f8

def z447 : W := mkw 0x5850280494010100 0x8b0a050092802020 0x0000000000000000 0x0000000000000000

def z448 : W := mkw 0x2582c7b0417818b8 0x44b058f6082f0317 0x2787c3e001f8383a 0x44f0f87c003f0707

def z449 : W := mkw 0x0000102908424620 0x00000205210848c4 0xf66033ff19c7c63b 0xfecc067fe338f8c7

def z450 : W := mkw 0xdfffefd6c2141002 0x1bfffdfad8428200 0xffffffffe63e3801 0xfffffffffcc7c700

def z451 : W := mkw 0xffffefdef7bfbadb 0x1ffffdfbdef7f75b 0xffffffffffffffff 0xffffffffffffffff

def z452 : W := mkw 0x2088c600621c10d0 0x041118c00c43821a 0x6999cf00e63807ff 0x6d3339e01cc700ff

def z453 : W := mkw 0x5dd83ea4bf6d05f0 0xcbbb07d497eda0be 0x7f983fe0fff807ff 0xeff307fc1fff00ff

def z454 : W := mkw 0x022c400017b5b001 0x0045880002f6b600 0xb66600001ffff801 0xf6ccc00003ffff00

def z455 : W := mkw 0x008287d240000002 0x001050fa48000000 0x000003e000000000 0x0000007c00000000

def z456 : W := mkw 0xdf7d680497b5b001 0x1befad0092f6b600 0xfffffc1ffffff801 0xffffff83ffffff00

def z457 : W := mkw 0x1d823fb81d6a0fb8 0x43b047f703ad41f7 0xff863ff81ffe3fff 0xfff0c7ff03ffc7ff

def z458 : W := mkw 0x0000100108004400 0x0000020021000880 0x106030071801c000 0x820c0600e3003800

def z459 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0x2f9fc00007f83800 0x45f3f80000ff0700

def z460 : W := mkw 0x0000000015200000 0x0000000002a40000 0x200000001ff80000 0x2400000003ff0000

def z461 : W := mkw 0x4058100dbe074740 0x880b0201b7c0e8e8 0x8078001ffe07c7c4 0x300f0003ffc0f8f8

def z462 : W := mkw 0x78d8fe0dfe1f57d0 0x8f1b1fc1bfc3eafa 0xd9f9fc1ffe3fc7c5 0xbb3f3f83ffc7f8f8

def z463 : W := mkw 0x1fa63ffb08c2ee28 0x23f4c7ff61185dc5 0xffe63fff19c7fe3b 0xfffcc7ffe338ffc7

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z465 : W := mkw 0x9f7d50201ff5b421 0x13efaa0403feb684 0xfffff3e01ffffe3b 0xfffffe7c03ffffc7

def z466 : W := mkw 0x58582804b6050140 0x8b0b050096c0a028 0xd8783c1fe60001c5 0x9b0f0783fcc00038

def z467 : W := mkw 0x2000400000181898 0x0400080000030313 0x200000000038383a 0x0400000000070707

def z468 : W := mkw 0x18803e001c080590 0x031007c0038100b2 0x79803f001e3807ff 0xef3007e003c700ff

def z469 : W := mkw 0x58d2af14c0000000 0x0b1a55e298000000 0xd9ffff1fe0000001 0xdb3fffe3fc000000

def z470 : W := mkw 0x02a6977b48c2ee28 0x2054d2ef69185dc5 0xfffffffff9c7fe3b 0xffffffffff38ffc7

def z471 : W := mkw 0x1850000000000000 0x030a000000000000 0x9878000000000001 0x930f000000000000

def z472 : W := mkw 0x5dd83e8dbf2f47d0 0xcbbb07d1b7e5e8fa 0xd9f83c1ffe3fc7c5 0xbb3f0783ffc7f8f8

def z473 : W := mkw 0x1d802ea0156801b0 0x43b005d402ad0036 0x2f800fe007f801fe 0x45f001fc00ff003f

def z474 : W := mkw 0x208affb86a5e1ff8 0x44115ff70d4bc3ff 0xe99ffff8e63e3fff 0x7d33ffff1cc7c7ff

def z475 : W := mkw 0x1d803ea008400420 0x03b007d401080084 0x7f803fe019c0063b 0xeff007fc033800c7

def z476 : W := mkw 0x208ad7387f7e1ff8 0x44115ae70fefc3ff 0xe99fcf18fffe3fff 0x7d33f9e31fffc7ff

def z477 : W := mkw 0x9f75000015a1a001 0x13eea00002b43400 0x9fffc00019c1c001 0xd3fff80003383800

def z478 : W := mkw 0x0080060000000000 0x001000c000000000 0x49800f0000000001 0x493001e000000000

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0x600003000000063b 0x6c000060000000c7

def z480 : W := mkw 0x0224106b08c2e620 0x2044820d61185cc4 0xd66030ff19c7c601 0xbacc061fe338f8c0

def z481 : W := mkw 0x1d00288015200100 0x43a0051002a40020 0x0000000000000000 0x0000000000000000

def z482 : W := mkw 0x0000000015280190 0x4000000002a50032 0x00000000063801c4 0x0000000000c70038

def z483 : W := mkw 0x02a6875240000000 0x0054d0ea48000000 0xdfffffffe0000001 0xdbfffffffc000000

def z484 : W := mkw 0xbfffffb87fffbff9 0x57fffff70ffff7ff 0xfffffff8ffffffff 0xffffffff1fffffff

def z485 : W := mkw 0x0008400002141000 0x0001080000428200 0x20000000063e3800 0x2400000000c7c700

def z486 : W := mkw 0xdff7afd6d5280192 0x5bfef5fadaa50032 0xdfffffffe63801c5 0xdbfffffffcc70038

def z487 : W := mkw 0x022400000080a000 0x0044800000101400 0x1660000019c1c000 0x82cc000003383800

def z488 : W := mkw 0x20828718600a0ad8 0x041050e30c01415b 0xe0060f18e0063fff 0x7c00c1e31c00c7ff

def z489 : W := mkw 0x5d5038a59d614520 0xcbaa0714b3ac28a4 0x166030e719c1c000 0x82cc061ce3383800

def z490 : W := mkw 0xc2f7afd6c0000002 0x185ef5fad8000000 0xc07fffffe0000000 0x180ffffffc000000

def z491 : W := mkw 0x9ff7871040000000 0x13fef0e208000000 0xdfffcf18e0000001 0xdbfff9e31c000000

def z492 : W := mkw 0x200ac11862161a48 0x040158230c42c349 0xe01fc318e0063e3b 0x7c03f8631c00c7c7

def z493 : W := mkw 0x9d59400017351001 0x13ab280002e6a200 0xa99fc000063e3801 0x7533f80000c7c700

def z494 : W := mkw 0x0226117308c0ec28 0x2044c22e61181d85 0x366633e719c1f83a 0xc6ccc67ce3383f07

def z495 : W := mkw 0x000010201d600520 0x4000020403ac00a4 0x0000000019c00000 0x0000000003380000

def z496 : W := mkw 0x0580068000000000 0x00b000d000000000 0x078003e000000000 0x40f0007c00000000

def z497 : W := mkw 0x1d0038a01d600520 0x43a0071403ac00a4 0x5e003ce01fc007c5 0xabc0079c03f800f8

def z498 : W := mkw 0x872d400003b4b001 0x10e5a80000769600 0xaf9fc00007fe3801 0x75f3f80000ffc700

def z499 : W := mkw 0xc7a7afd6c0000002 0x18f4f5fad8000000 0x4787ffffe0000000 0x48f0fffffc000000

def z500 : W := mkw 0x3d88fea07f7c15f0 0x47b11fd40fef82be 0x7f99ffe0fff807ff 0xeff33ffc1fff00ff

def z501 : W := mkw 0x9f77015200000000 0x13eee02a40000000 0xdffff3ff00000001 0xdbfffe7fe0000000

def z502 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0x48183c1fe60007c4 0x09030783fcc000f8

def z503 : W := mkw 0xa7afc71863bebad9 0x14f5f8e30c77d75b 0xef9fcf18e7fe3fff 0x7df3f9e31cffc7ff

def z504 : W := mkw 0x585a397fbe474f68 0xab0b472ff7c8e9ed 0xd8783ffffe07c7ff 0xbb0f07ffffc0f8ff

def z505 : W := mkw 0xdf7538e69d600522 0x5beea71cd3ac00a4 0x166030e719c00000 0x82cc061ce3380000

def z506 : W := mkw 0x000810293ec7ef68 0xa001020527d8fded 0x200000001fc7fffe 0x2400000003f8ffff

def z507 : W := mkw 0x208ad77b6a5e5ef8 0x24115aef6d4bcbdf 0xe99fffffe63e3fff 0x7d33fffffcc7c7ff

def z508 : W := mkw 0x00803ea0084805b0 0x401007d4010900b6 0x76003fe019c007ff 0xeec007fc033800ff

def z509 : W := mkw 0x1fa63ff21d6805b0 0x43f4c7fe43ad00b6 0xffe63fff1ff807ff 0xfffcc7ffe3ff00ff

def z510 : W := mkw 0x9fa7bff25d6805b2 0x53f4f7fe4bad00b6 0x7f87ffe01ff807ff 0xeff0fffc03ff00ff

def z511 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0x4999cf18e63807fe 0x093339e31cc700ff

def z512 : W := mkw 0x00884600021c1090 0x001108c000438212 0xe99fcf00063e3fff 0x7d33f9e000c7c7ff

def z513 : W := mkw 0x0000000800020200 0x0000000100004040 0xc000001800060601 0x380000030000c0c0

def z514 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0x0f9fcfe0e0000000 0x41f3f9fc1c000000

def z515 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0x08180c00fe07c7c4 0x210301801fc0f8f8

def z516 : W := mkw 0x3d88ee80773c11d0 0x47b11dd00ee7823a 0x0999cc00e63801c4 0x013339801cc70038

def z517 : W := mkw 0x20808600600800d0 0x041010c00c01001a 0x00000c00e00001c4 0x000001801c000038

def z518 : W := mkw 0x5858382dbec7ef68 0xab0b0705b7d8fded 0xf8783c1fffc7ffff 0xbf0f0783fff8ffff

def z519 : W := mkw 0x0002117b08424e28 0x2000422f610849c5 0xe00633ff00063e3b 0x7c00c67fe000c7c7

def z520 : W := mkw 0x2008c00062141040 0x040118000c428208 0x0019c000e0000000 0x000338001c000000

def z521 : W := mkw 0xdff7aff6c16800b2 0x5bfef5fed82d0016 0xffffffffe1f8003b 0xdffffffffc3f0007

def z522 : W := mkw 0x872500c200000002 0x10e4a01840000000 0x060000e000000000 0x00c0001c00000000

def z523 : W := mkw 0x9fffc71057b5b001 0x13fff8e20af6b600 0xffffcf18fffff801 0xfffff9e31fffff00

def z524 : W := mkw 0x9fa57ea01df8b5b1 0x53f4afd403bf16b6 0x7f87ffe01ff83fff 0xeff0fffc03ff07ff

def z525 : W := mkw 0x0002011000000808 0x0000402200000101 0x200603000000383a 0x4400c06000000707

def z526 : W := mkw 0xdfffefd6d7351003 0x1bfffdfadae6a200 0xdfffffffe6380001 0xdbfffffffcc70000

def z527 : W := mkw 0x87a787d240000002 0x10f4f0fa48000000 0xcf9fcff8e0000001 0x59f3f9ff1c000000

def z528 : W := mkw 0xdd51288480000002 0x1baa251090000000 0x0000000000000000 0x0000000000000000

def z529 : W := mkw 0x827f415b0297fa09 0x304fe82b6052ff41 0x807fc01f0007f800 0x100ff803e000ff00

def z530 : W := mkw 0x0008000822060240 0x000100010440c048 0x80180018e0060000 0x100300031c00c000

def z531 : W := mkw 0xa7a7c71041b8b899 0x14f4f8e208371713 0x2787c30001f8383a 0x44f0f860003f0707

def z532 : W := mkw 0x5a7c380dbe87e740 0x8b4f8701b7d0fce8 0xfe7e3c1fffc7ffc5 0xffcfc783fff8fff8

def z533 : W := mkw 0xdff5ae84c0000002 0x1bfeb5d098000000 0x9fffcc00e0000001 0xd3fff9801c000000

def z534 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0xa066001f19c7fe3a 0x340cc003e338ffc7

def z535 : W := mkw 0x58d83e0dbe0f47d0 0x8b1b07c1b7c1e8fa 0xf9f83f1ffe3fc7ff 0xff3f07e3ffc7f8ff

def z536 : W := mkw 0x5858382dbf6f47f0 0xcb0b0705b7ede8fe 0xf8783c1fffffc7ff 0xbf0f0783fffff8ff

def z537 : W := mkw 0x0002113808420e28 0x00004227010841c5 0xf60633f819c63e3b 0xfec0c67f0338c7c7

def z538 : W := mkw 0x58d83eadbe4f47f0 0xcb1b07d5b7c9e8fe 0xd8783ffffe07c7ff 0xbb0f07ffffc0f8ff

def z539 : W := mkw 0x87a797fb48c2ee2a 0x30f4f2ff69185dc5 0xf7e7f3ff19c7fe3b 0xfefcfe7fe338ffc7

def z540 : W := mkw 0xdff5aec6c0000002 0x1bfeb5d8d8000000 0x1ff9fce7e0000000 0x83ff3f9cfc000000

def z541 : W := mkw 0x208ac71862161a48 0x041158e30c42c349 0xc99fcf18e0063801 0x5933f9e31c00c700

def z542 : W := mkw 0x0008000036050140 0x8001000006c0a028 0x00000000060001c4 0x0000000000c00038

def z543 : W := mkw 0x0226017a00c2aa28 0x2044c02f40185545 0xe60603f801c63e3b 0x7cc0c07f0038c7c7

def z544 : W := mkw 0x9f75400001b0b001 0x13eea80000361600 0xbfffc00001f83801 0xd7fff800003f0700

def z545 : W := mkw 0x585a391dbe074f48 0x8b0b4723b7c0e9e9 0xf87e3f1ffe07ffff 0xff0fc7e3ffc0ffff

def z546 : W := mkw 0xbdd9c600773d10d1 0x17bb38c00ee7a21a 0x0999cc00e63801c4 0x013339801cc70038

def z547 : W := mkw 0xdff7bfdfe8024742 0x9bfef7fbfd0048e8 0xdfffffffe00007c5 0xdbfffffffc0000f8

def z548 : W := mkw 0x20084008221e1ad8 0x040108010443c35b 0xa99fc000063e3fff 0x7533f80000c7c7ff

def z549 : W := mkw 0x9f7d50201ffdb5b1 0x53efaa0403ffb6b6 0xbfffc0001fffffff 0xf7fff80003ffffff

def z550 : W := mkw 0x022601520080a808 0x2044c02a40101501 0x0006000000003800 0x0000c00000000700

def z551 : W := mkw 0x0226117308c0e420 0x2044c22e61181c84 0xd66633ff19c1c001 0xdaccc67fe3383800

def z552 : W := mkw 0x0002113908c2ee28 0x2000422721185dc5 0xe006031819c7fe3b 0x7c00c0630338ffc7

def z553 : W := mkw 0xdff7bfd7dc014502 0x9bfef7fafb8028a0 0xdffffffff801c001 0xdbffffffff003800

def z554 : W := mkw 0x3d82bfb87d6a0ff8 0x47b057f70fad41ff 0x7f803ff8fff807ff 0xeff007ff1fff00ff

def z555 : W := mkw 0x0002117b08c2ee28 0x2000422f61185dc5 0x600033ff19c7fe3a 0x2c00067fe338ffc7

def z556 : W := mkw 0x20884608221e1ad8 0x041108c10443c35b 0x69800f00063e3fff 0x6d3001e000c7c7ff

def z557 : W := mkw 0x0000002000400020 0x0000000400080004 0x260003e001c0003a 0x44c0007c00380007

def z558 : W := mkw 0x1800280000000000 0x0300050000000000 0x58003c0000000001 0x8b00078000000000

def z559 : W := mkw 0x1d802e8015280190 0x43b005d002a50032 0x69800f00063807ff 0x6d3001e000c700ff

def z560 : W := mkw 0x0000106308404420 0x2000020c61080884 0x000030e700000000 0x0000061ce0000000

def z561 : W := mkw 0x0000100908024600 0x00000201210048c0 0x4000301f00000600 0x08000603e00000c0

def z562 : W := mkw 0x3faefffb7ffefff8 0x67f5dfff6fffdfff 0xffffffffffffffff 0xffffffffffffffff

def z563 : W := mkw 0x9f7f415b17b7fa09 0x33efe82b62f6ff41 0xbfffc01f1ffff801 0xf7fff803e3ffff00

def z564 : W := mkw 0x9d51000015210001 0x13aa200002a42000 0x0000000000000000 0x0000000000000000

def z565 : W := mkw 0x2088c608621e12d0 0x041118c10c43c25a 0xc999cc18e63e07c5 0x393339831cc7c0f8

def z566 : W := mkw 0x0080060000080090 0x001000c000010012 0x40000f00000007fe 0x080001e0000000ff

def z567 : W := mkw 0xdff7bff6dd600522 0x5bfef7fedbac00a4 0xdffffffff9c00001 0xdbffffffff380000

def z568 : W := mkw 0x400028c680000002 0x08000518d0000000 0x000030e700000000 0x0000061ce0000000

def z569 : W := mkw 0x0226015200000000 0x0044c02a40000000 0x8066001f00000000 0x100cc003e0000000

def z570 : W := mkw 0x87a787f240c0a82a 0x30f4f0fe48181505 0x2787c3e001c0383a 0x44f0f87c00380707

def z571 : W := mkw 0x0002015b00024a08 0x2000402b60004941 0x0000001f00000000 0x00000003e0000000

def z572 : W := mkw 0x4082bfffc8424e2a 0x281057fff90849c5 0x40003fffe000063a 0x080007fffc0000c7

def z573 : W := mkw 0x8725000001a0a001 0x10e4a00000341400 0x0600000001c00000 0x00c0000000380000

def z574 : W := mkw 0x1d803ea0084805b0 0x43b007d4010900b6 0x5f803fe0000007ff 0xcbf007fc000000ff

def z575 : W := mkw 0x0008000822060240 0x000100010440c048 0x00000000060607c4 0x2000000000c0c0f8

def z576 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0x2187c300063e3ffe 0x6430f86000c7c7ff

def z577 : W := mkw 0xc27f815fe2074242 0x984ff02bfc40e848 0x807fc01fe007c000 0x100ff803fc00f800

def z578 : W := mkw 0xdf7d380dbe074740 0x9befa701b7c0e8e8 0xdffffc1ffe07c7c5 0xfbffff83ffc0f8f8

def z579 : W := mkw 0xc27fc156c295b003 0x184ff82ad852b600 0x807fc01fe007f800 0x100ff803fc00ff00

def z580 : W := mkw 0x608aefdee21e1ada 0x0c115dfbdc43c35b 0xe99fffffe63e3fff 0x7d33fffffcc7c7ff

def z581 : W := mkw 0x208ac710621c10d0 0x041158e20c43821a 0xc99fcf18e63801c5 0x5933f9e31cc70038

def z582 : W := mkw 0x877d400003b5b001 0x10efa8000076b600 0xa7ffc00001fff800 0x54fff800003fff00

def z583 : W := mkw 0x0000102008400420 0x0000020401080084 0x160030e019c00000 0x82c0061c03380000

def z584 : W := mkw 0x9f7d50631ff5f421 0x33efaa0c63febe84 0xbffff0e71ffff801 0xf7fffe1ce3ffff00

def z585 : W := mkw 0x58583804be050540 0x8b0b070097c0a0a8 0x58183c00fe0007c5 0xab0307801fc000f8

def z586 : W := mkw 0x3d8aef98773e1bd8 0x47b15df30ee7c37b 0xe99fcf18e63e3fff 0x7d33f9e31cc7c7ff

def z587 : W := mkw 0x4080ae84c0000002 0x081015d098000000 0x00000c00e0000000 0x000001801c000000

def z588 : W := mkw 0x4082bff6c84805b2 0x481057fed90900b6 0x40003fffe00007fe 0x080007fffc0000ff

def z589 : W := mkw 0x1d0038a01d600520 0x43a0071403ac00a4 0x3f8030e01ff80001 0xe7f0061c03ff0000

def z590 : W := mkw 0x22aec75b629efad8 0x2455d8eb6c53df5b 0xe9ffcf1fe63fffff 0x7d3ff9e3fcc7ffff

def z591 : W := mkw 0x0224006200c0a020 0x2044800c40181404 0x060000e001c00000 0x00c0001c00380000

def z592 : W := mkw 0x0008000002040000 0x0001000000408000 0x8818000006060001 0x3103000000c0c000

def z593 : W := mkw 0x0002011000000000 0x0000402200000000 0xc006031800000001 0x5800c06300000000

def z594 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0x660633ff01c03e3a 0x4cc0c67fe03807c7

def z595 : W := mkw 0x0002015200000000 0x0000402a40000000 0x400033ff00000000 0x0800067fe0000000

def z596 : W := mkw 0x3d8aef98621e1ad8 0x07b15df30c43c35b 0xff9ffff8e63e3fff 0xfff3ffff1cc7c7ff

def z597 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x1f803ce01ff801c4 0x83f0079c03ff0038

def z598 : W := mkw 0x0000102108c0e420 0x2000020421181c84 0x0000000019c1c000 0x0000000003383800

def z599 : W := mkw 0x0008000922074240 0x800100012440e848 0x000000000007c000 0x000000000000f800

def z600 : W := mkw 0x78dabf1dfe0f4fd8 0x8f1b57e3bfc1e9fb 0xd8783f1ffe07c7ff 0xbb0f07e3ffc0f8ff

def z601 : W := mkw 0x185810091e074600 0x030b020123c0e8c0 0xd878301f1e07c601 0xbb0f0603e3c0f8c0

def z602 : W := mkw 0xc2f78756c0000002 0x185ef0ead8000000 0xc9ffcf1fe0000001 0x593ff9e3fc000000

def z603 : W := mkw 0x0224106308c0e420 0x2044820c61181c84 0x766033e719c1c63b 0xeecc067ce33838c7

def z604 : W := mkw 0xc7f787d6c0000002 0x18fef0fad8000000 0x87ffc3ffe0000000 0x50fff87ffc000000

def z605 : W := mkw 0x2082c71040181898 0x041058e208030313 0x6987cf0006383fff 0x6d30f9e000c707ff

def z606 : W := mkw 0x585038049c000500 0x0b0a0700938000a0 0xd8783c1ffe0007c5 0xbb0f0783ffc000f8

def z607 : W := mkw 0x000010291deaefb8 0x6000020523bd5df7 0x200000001ffffffe 0x2400000003ffffff

def z608 : W := mkw 0x9f7f411817b7ba09 0x13efe82302f6f741 0xffffc3181ffffe3b 0xfffff86303ffffc7

def z609 : W := mkw 0x1d08400017b5b001 0x03a1080002f6b600 0x3f8000001ffff801 0xe7f0000003ffff00

def z610 : W := mkw 0xdff53ee69d6805b2 0x5bfea7dcd3ad00b6 0x7fe03fe71ff807ff 0xeffc07fce3ff00ff

def z611 : W := mkw 0x1d802e8000000000 0x03b005d000000000 0x09800c0000000000 0x0130018000000000

def z612 : W := mkw 0x9f7d000016050000 0x13efa00002c0a000 0x9fffc0001e07c001 0xf3fff80003c0f800

def z613 : W := mkw 0x0082871840020a08 0x001050e308004141 0xe99fcf18e0063e3b 0x7d33f9e31c00c7c7

def z614 : W := mkw 0xc277917fc8c2ee2a 0x384ef22ff9185dc5 0xf67ff3fff9c7fe3b 0xfecffe7fff38ffc7

def z615 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0x366000001ffff800 0xa6cc000003ffff00

def z616 : W := mkw 0x8501400001301001 0x10a0280000260200 0x0181c00000380000 0x0030380000070000

def z617 : W := mkw 0x9f25400015b0b001 0x13e4a80002b61600 0x3f87c0001ff83801 0xe7f0f80003ff0700

def z618 : W := mkw 0xdf7fc156d7b5b003 0x1beff82adaf6b600 0xbfffc01ffffff801 0xf7fff803ffffff00

def z619 : W := mkw 0xdfffafd6d6050002 0x1bfff5fadac0a000 0xdffffffffe07c001 0xfbffffffffc0f800

def z620 : W := mkw 0x1d0010201d600420 0x03a0020403ac0084 0x7f8033e01ff8063b 0xeff0067c03ff00c7

def z621 : W := mkw 0xbf7d400837bfbad9 0x17efa80106f7f75b 0xbfffc0001fffffff 0xf7fff80003ffffff

def z622 : W := mkw 0x5a76397f88c2ee28 0x2b4ec72ff1185dc5 0xfe7e3ffff9c7fe3b 0xffcfc7ffff38ffc7

def z623 : W := mkw 0xdf7729d680000002 0x1beee53ad0000000 0xd66633ff00000001 0xdaccc67fe0000000

def z624 : W := mkw 0xda77a956c0000002 0x1b4ef52ad8000000 0xd87ffc1fe0000001 0x9b0fff83fc000000

def z625 : W := mkw 0x00803ea01d6805b0 0x401007d403ad00b6 0x60003fe01ff807fe 0x2c0007fc03ff00ff

def z626 : W := mkw 0x5858280496050000 0x0b0b050092c0a000 0xd8783c1ffe07c001 0xbb0f0783ffc0f800

def z627 : W := mkw 0x1d0038a01d6805b0 0x43a0071403ad00b6 0x360030e01ff807fe 0xa6c0061c03ff00ff

def z628 : W := mkw 0x1d802ea0016800b0 0x43b005d4002d0016 0x7f803fe001f8003b 0xcff007fc003f0007

def z629 : W := mkw 0x200a4118221e1ad8 0x040148230443c35b 0xe0060318063e3fff 0x7c00c06300c7c7ff

def z630 : W := mkw 0x2008400822161a48 0x040108010442c349 0x0000000000063800 0x000000000000c700

def z631 : W := mkw 0x5d82afd6c0000002 0x0bb055fad8000000 0x5f803fffe0000001 0xcbf007fffc000000

def z632 : W := mkw 0xffffffdffe1f5fda 0x9ffffffbffc3ebfb 0xfffffffffe3fffff 0xffffffffffc7ffff

def z633 : W := mkw 0x18803ea01c4805b0 0x431007d4038900b6 0x58003fe01e0007ff 0xab0007fc03c000ff

def z634 : W := mkw 0x87a787d240000002 0x10f4f0fa48000000 0xd7e7f3ff00000001 0xdafcfe7fe0000000

def z635 : W := mkw 0x785af91dfe175f48 0x8f0b5f23bfc2ebe9 0xd87ffc1ffe07ffc5 0xbb0fff83ffc0fff8

def z636 : W := mkw 0x022e517b1ff7fe29 0x2045ca2f63feffc5 0xf66633ff1ffffe3b 0xfeccc67fe3ffffc7

def z637 : W := mkw 0x42a6bfffc8c2ee2a 0x2854d7fff9185dc5 0xf6663ffff9c7fe3b 0xfeccc7ffff38ffc7

def z638 : W := mkw 0xdf7538e788c0e422 0x3beea71cf1181c84 0x166030e719c1c000 0x82cc061ce3383800

def z639 : W := mkw 0x208ad7386a5e1ef8 0x04115ae70d4bc3df 0xff9ffff8fffe3fff 0xfff3ffff1fffc7ff

def z640 : W := mkw 0x58582804b6050140 0x8b0b050096c0a028 0x98780c00fe07c1c5 0xb30f01801fc0f838

def z641 : W := mkw 0xfffffffeff7e1ffa 0x5fffffffdfefc3ff 0xfffffffffffe3fff 0xffffffffffffc7ff

def z642 : W := mkw 0x58d2afd6c0000002 0x0b1a55fad8000000 0xd8783fffe0000001 0x9b0f07fffc000000

def z643 : W := mkw 0x827f517b0ad7fe29 0x304fea2f615affc5 0xf67ff3ff19c7fe3b 0xfecffe7fe338ffc7

def z644 : W := mkw 0x40580004a2050040 0x880b00009440a008 0x00180000e0000000 0x000300001c000000

def z645 : W := mkw 0x1d823ffb1d6a4fb8 0x63b047ff63ad49f7 0x7f803fff1ff807ff 0xeff007ffe3ff00ff

def z646 : W := mkw 0x9ffd6e8017bdb191 0x53ffadd002f7b632 0xbfffcc001ffff9c5 0xf7fff98003ffff38

def z647 : W := mkw 0x0080860040000000 0x001010c008000000 0x0999cc00e0000000 0x013339801c000000

def z648 : W := mkw 0xdf7d78059fb5f501 0x9befaf00b3f6bea0 0xbffff0071ffff801 0xf7fffe00e3ffff00

def z649 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0xc06633ff0007fe3a 0x180cc67fe000ffc7

def z650 : W := mkw 0x0000100008000400 0x0000020001000080 0x5000300018000601 0xaa000600030000c0

def z651 : W := mkw 0x20828718600a0ad8 0x041050e30c01415b 0x69800f18e63807ff 0x6d3001e31cc700ff

def z652 : W := mkw 0x827d400017b5b001 0x104fa80002f6b600 0xa07fc0001ffff800 0x340ff80003ffff00

def z653 : W := mkw 0x4050000480000000 0x080a000090000000 0x8078001fe0000000 0x100f0003fc000000

def z654 : W := mkw 0x02a63ffb08caefb8 0x6054c7ff61195df7 0xf6663fff19c7ffff 0xfeccc7ffe338ffff

def z655 : W := mkw 0x07a607f201e8a8b8 0x60f4c0fe403d1517 0x278603e001f8383a 0x44f0c07c003f0707

def z656 : W := mkw 0xdd596804b7351141 0x9bab2d0096e6a228 0x0999cc00e63801c4 0x013339801cc70038

def z657 : W := mkw 0x9f7d50093fb7f741 0x93efaa0127f6fee8 0xbfffc0001fffffc5 0xf7fff80003fffff8

def z658 : W := mkw 0x5850380d9c034700 0x8b0a0701b38068e0 0xd060301f1807c601 0xba0c0603e300f8c0

def z659 : W := mkw 0x1d803ea91deaefb8 0x63b007d523bd5df7 0x7f803fe01fffffff 0xeff007fc03ffffff

def z660 : W := mkw 0xdf7d380dbfa7e741 0x9befa701b7f4fce8 0xde783c1fffc7c7c5 0xbbcf0783fff8f8f8

def z661 : W := mkw 0x827d40000295b001 0x104fa8000052b600 0xa9ffc000063ff801 0x753ff80000c7ff00

def z662 : W := mkw 0x2002c11040101808 0x0400582208020301 0x0007c00000003800 0x0000f80000000700

def z663 : W := mkw 0x1f24000015a0a000 0x03e4800002b41400 0xbfe600001ffff801 0xf7fcc00003ffff00

def z664 : W := mkw 0x8227815240000002 0x1044f02a48000000 0x0007c00000000000 0x0000f80000000000

def z665 : W := mkw 0xdfffffdfffb7f743 0x9bfffffbfff6fee8 0xffffffffffffffc5 0xfffffffffffffff8

def z666 : W := mkw 0x9a7d40001695b001 0x134fa80002d2b600 0x987fc0001e07f801 0xb30ff80003c0ff00

def z667 : W := mkw 0x022e117b3ec7ef68 0xa045c22f67d8fded 0xf66633ff1fc7ffff 0xfeccc67fe3f8ffff

def z668 : W := mkw 0x000038a008400520 0x40000714010800a4 0x000030e000000000 0x0000061c00000000

def z669 : W := mkw 0x000010001c000500 0x00000200038000a0 0x000000001e0007c4 0x2000000003c000f8

def z670 : W := mkw 0x9f7d400002141000 0x13efa80000428200 0xbfffc000063e3801 0xf7fff80000c7c700

def z671 : W := mkw 0x1fa43ea01de8a5b0 0x43f487d403bd14b6 0xffe63fe01fffffff 0xfffcc7fc03ffffff

def z672 : W := mkw 0x0226117208c0ac28 0x2044c22e41181585 0x760633e019c03e3b 0xeec0c67c033807c7

def z673 : W := mkw 0x9ff52e8000000000 0x13fea5d000000000 0xdfffffe000000001 0xdbfffffc00000000

def z674 : W := mkw 0x0226115b08024600 0x0044c22b610048c0 0xd66633ff1807c601 0xfaccc67fe300f8c0

def z675 : W := mkw 0x2082c718401a1a98 0x041058e308034353 0xe187c318003e3e3b 0x7c30f8630007c7c7

def z676 : W := mkw 0x0500000001200000 0x00a0000000240000 0x2780000001f80000 0x44f00000003f0000

def z677 : W := mkw 0x5a7438679cc1e520 0xab4e870cf3983ca4 0x166030e719c1c000 0x82cc061ce3383800

def z678 : W := mkw 0x5858000db6074240 0x8b0b0001b6c0e848 0x9878001ffe07c001 0xb30f0003ffc0f800

def z679 : W := mkw 0xdf7538059da1e501 0x9beea700b3b43ca0 0x1660300719c1c000 0x82cc0600e3383800

def z680 : W := mkw 0x00820718000a0a98 0x001040e300014153 0xe9860f18063e3fff 0x7d30c1e300c7c7ff

def z681 : W := mkw 0x427e117faac7ee68 0xa84fc22ff558fdcd 0xf67e33fff9c7fe3b 0xfecfc67fff38ffc7

def z682 : W := mkw 0x0058000002050000 0x000b00000040a000 0x807800000007c000 0x100f00000000f800

def z683 : W := mkw 0xbffdc60077bdb0d1 0x17ffb8c00ef7b61a 0xbfffcc00fffff9c5 0xf7fff9801fffff38

def z684 : W := mkw 0xdf7528c695a1a003 0x1beea518d2b43400 0x166030e719c1c000 0x82cc061ce3383800

def z685 : W := mkw 0xddd1ae84c0000002 0x1bba35d098000000 0xd9f9fc1fe0000001 0x9b3f3f83fc000000

def z686 : W := mkw 0x9f75400015b1b001 0x13eea80002b63600 0x37e7c00019f9f800 0xc6fcf800033f3f00

def z687 : W := mkw 0x000010011c014500 0x80000200238028a0 0x000000001801c000 0x0000000003003800

def z688 : W := mkw 0x208ac710421c1898 0x041158e208438313 0xa99fc300063e383b 0x7533f86000c7c707

def z689 : W := mkw 0x0226117208400420 0x0044c22e41080084 0xf66633ff19c0063b 0xfeccc67fe33800c7

def z690 : W := mkw 0x1d887ea01f7c15b0 0x43b10fd403ef82b6 0xff9fffe01ffe3fff 0xfff3fffc03ffc7ff

def z691 : W := mkw 0x2088c608621e1ad8 0x041118c10c43c35b 0x2999cc00e63e3ffe 0x253339801cc7c7ff

def z692 : W := mkw 0x0002117b08424e28 0x2000422f610849c5 0x760033ff19c0063b 0xeec0067fe33800c7

def z693 : W := mkw 0x2082c718601a1ad8 0x041058e30c03435b 0x6187cf18e0383ffe 0x4c30f9e31c0707ff

def z694 : W := mkw 0x608aff1dea1e5fd8 0x8c115fe3bd43cbfb 0xe99fff1fe63e3fff 0x7d33ffe3fcc7c7ff

def z695 : W := mkw 0xfddbef9ce21e1ada 0x1fbb7df39c43c35b 0xe99fcf18e63e3fff 0x7d33f9e31cc7c7ff

def z696 : W := mkw 0x00000020016800b0 0x40000004002d0016 0x2000000001f8003a 0x04000000003f0007

def z697 : W := mkw 0x0226015b0082ea08 0x2044c02b60105d41 0xd66633ff0007f801 0xdaccc67fe000ff00

def z698 : W := mkw 0x5a76295680000000 0x0b4ec52ad0000000 0xde7e3fffe0000001 0xdbcfc7fffc000000

def z699 : W := mkw 0x1d00000015200000 0x03a0000002a40000 0x1600000019c00000 0x82c0000003380000

def z700 : W := mkw 0xffffefdee2161a4a 0x1ffffdfbdc42c349 0xdfffffffe0063801 0xdbfffffffc00c700

def z701 : W := mkw 0x208ad7196a1e5ed8 0x04115ae32d43cbdb 0xf9ffff1ffe3fffff 0xff3fffe3ffc7ffff

def z702 : W := mkw 0x585838059e054500 0x8b0b0700b3c0a8a0 0x987830071e07c001 0xb30f0600e3c0f800

def z703 : W := mkw 0xa7afc7da621e1ada 0x14f5f8fb4c43c35b 0xef9fcff8e63e3fff 0x7df3f9ff1cc7c7ff

def z704 : W := mkw 0x4008380dbe074740 0x88010701b7c0e8e8 0x40003c1ffe07c7c4 0x28000783ffc0f8f8

def z705 : W := mkw 0x5850280480000000 0x0b0a050090000000 0x08180c00e0000000 0x010301801c000000

def z706 : W := mkw 0x22aec718629ebad8 0x0455d8e30c53d75b 0xffffcf18ffffffff 0xfffff9e31fffffff

def z707 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0xfe783c1fffc7c7c5 0xffcf0783fff8f8f8

def z708 : W := mkw 0xd859780dbe175741 0x9b0b2f01b7c2eae8 0xd879fc1ffe07c7c5 0xbb0f3f83ffc0f8f8

def z709 : W := mkw 0x9d5b517b1f775e29 0x33ab6a2f63eeebc5 0x4999f3ff0638063a 0x09333e7fe0c700c7

def z710 : W := mkw 0x3d0af9b87f761f68 0x47a15f370feec3ed 0x961ff0f8f9c63800 0x92c3fe1f1f38c700

def z711 : W := mkw 0x9f2d400017b5b001 0x13e5a80002f6b600 0x3f87c0001ffff801 0xe7f0f80003ffff00

def z712 : W := mkw 0xc2779176dd6805b2 0x584ef22edbad00b6 0xa07fc01ffff807fe 0x340ff803ffff00ff

def z713 : W := mkw 0xdf7d680497b5b001 0x1befad0092f6b600 0xbffff0071ffff801 0xf7fffe00e3ffff00

def z714 : W := mkw 0xdff7afd6d5200002 0x1bfef5fadaa40000 0xdfffffffe6380001 0xdbfffffffcc70000

def z715 : W := mkw 0x7858780dbe175f48 0x8f0b0f01b7c2ebe9 0xd8783c1ffe07ffc5 0xbb0f0783ffc0fff8

def z716 : W := mkw 0x1dd03ea01d6805b0 0x43ba07d403ad00b6 0xfff83fe01ff807ff 0xffff07fc03ff00ff

def z717 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0x9fffc0001ffff800 0x93fff80003ffff00

def z718 : W := mkw 0x9d81bea05d6805b2 0x53b037d40bad00b6 0x7f81ffe01ff807ff 0xeff03ffc03ff00ff

def z719 : W := mkw 0x208ac75b621e5ad8 0x241158eb6c43cb5b 0xe99fcf1fe63e3fff 0x7d33f9e3fcc7c7ff

def z720 : W := mkw 0x0082875240000000 0x001050ea48000000 0xc99fffffe0000001 0x5933fffffc000000

def z721 : W := mkw 0xdf7d680497b5b101 0x9befad0092f6b620 0xbfffc0001ffff801 0xf7fff80003ffff00

def z722 : W := mkw 0x0224106b08c2ee28 0x2044820d61185dc5 0x766033e719c7fe3b 0xeecc067ce338ffc7

def z723 : W := mkw 0xbff7871875abaad9 0x17fef0e30eb5755b 0x56600f18f9c1c7fe 0x8acc01e31f3838ff

def z724 : W := mkw 0xddd1beadc8c2ee2a 0x3bba37d5b9185dc5 0x2999cc00f9c7fe3a 0x253339801f38ffc7

def z725 : W := mkw 0xdff7afd6d5280092 0x1bfef5fadaa50012 0xfffffffffff807ff 0xffffffffffff00ff

def z726 : W := mkw 0x0226917b48c2ee28 0x2044d22f69185dc5 0xf67ff3fff9c7fe3b 0xfecffe7fff38ffc7

def z727 : W := mkw 0x0226117b28c2ee68 0x2044c22f65185dcd 0xf6663ffff9c7ffff 0xfeccc7ffff38ffff

def z728 : W := mkw 0xfff7afd6c008089a 0x1ffef5fad8010113 0xdfffffffe000003b 0xdbfffffffc000007

def z729 : W := mkw 0x4000380da8024740 0x88000701b50048e8 0x50603c1ff801c7c4 0x8a0c0783ff0038f8

def z730 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0x299fcf00e63e3ffe 0x6533f9e01cc7c7ff

def z731 : W := mkw 0xddd3afd6c0000002 0x1bba75fad8000000 0xd9f9ffffe0000001 0x9b3f3ffffc000000

def z732 : W := mkw 0x20829739684a4ef8 0x241052e72d0949df 0x40000f18e00007fe 0x080001e31c0000ff

def z733 : W := mkw 0x408aefd6d7b5b003 0x08115dfadaf6b600 0x60003ffffffff800 0x2c0007ffffffff00

def z734 : W := mkw 0xddd13ea49d6805b2 0x5bba27d493ad00b6 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z735 : W := mkw 0x1d80bea05d6805b0 0x43b017d40bad00b6 0x7f99ffe0fff807ff 0xeff33ffc1fff00ff

def z736 : W := mkw 0x87a7c7f241f8b0b3 0x50f4f8fe483f1616 0x2787c3e001f8383a 0x44f0f87c003f0707

def z737 : W := mkw 0x87af97db7e074742 0x90f5f2fb6fc0e8e8 0x0787c3e01e07c7c4 0x60f0f87c03c0f8f8

def z738 : W := mkw 0xddd1ae84c0000002 0x1bba35d098000000 0xdff9ffffe0000001 0xdbff3ffffc000000

def z739 : W := mkw 0x1d0038a01d6805b0 0x43a0071403ad00b6 0x760033e01ff807ff 0xeec0067c03ff00ff

def z740 : W := mkw 0x0224106308c0e420 0x2044820c61181c84 0xf66633e719c7fe3b 0xfeccc67ce338ffc7

def z741 : W := mkw 0xc277a9d6c0000002 0x184ef53ad8000000 0x807ff0ffe0000000 0x100ffe1ffc000000

def z742 : W := mkw 0x5d5838adbf674760 0xcbab0715b7ece8ec 0xfe783fffffc7c7ff 0xffcf07fffff8f8ff

def z743 : W := mkw 0x9f75400015b1b001 0x13eea80002b63600 0xb7e7c00019fff801 0xf6fcf800033fff00

def z744 : W := mkw 0xddd9ee84d73d1193 0x5bbb3dd09ae7a232 0x0999cc00e63801c4 0x013339801cc70038

def z745 : W := mkw 0xdff7afd6c1280092 0x5bfef5fad8250012 0xdfffffffe0380001 0xdbfffffffc070000

def z746 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0xb66633ff19c7f83a 0xd6ccc67fe338ff07

def z747 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0xffffffffe6380001 0xfffffffffcc70000

def z748 : W := mkw 0x45d806ada36f42f0 0xc8bb00d5b46de85e 0xa7f803ffe1ffc03a 0x54ff007ffc3ff807

def z749 : W := mkw 0x5dd03ea49d6805b0 0x4bba07d493ad00b6 0x7fe03fe71ff807ff 0xeffc07fce3ff00ff

def z750 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0xffe03fff1ff807ff 0xfffc07ffe3ff00ff

def z751 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0xff863fe01ffe3fff 0xfff0c7fc03ffc7ff

def z752 : W := mkw 0x9f7d404217b5b001 0x13efa80842f6b600 0xbffff0e71ffff801 0xf7fffe1ce3ffff00

def z753 : W := mkw 0x9f7d688017b5b001 0x13efad1002f6b600 0xbffff0e01ffff801 0xf7fffe1c03ffff00

def z754 : W := mkw 0x0008000922064240 0x000100012440c848 0xc8780c1fe607c7c5 0x390f0183fcc0f8f8

def z755 : W := mkw 0x9dd13ea01d6805b0 0x53ba27d403ad00b6 0x7f99ffe01ff807ff 0xeff33ffc03ff00ff

def z756 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0xd66633ff19c7fe3a 0x9accc67fe338ffc7

def z757 : W := mkw 0x5858380daa074740 0x8b0b0701b540e8e8 0xd8783c1fe007c7c5 0x9b0f0783fc00f8f8

def z758 : W := mkw 0xdff7afd6d4000102 0x1bfef5fada800020 0xdfffffffe60001c5 0xdbfffffffcc00038

def z759 : W := mkw 0x82fd7ea00addb5b1 0x505fafd4015bb6b6 0xc07fffe00007fffe 0x180ffffc0000ffff

def z760 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0x97fff3ffe0000000 0xd2fffe7ffc000000

def z761 : W := mkw 0x000010201d6805b0 0x4000020403ad00b6 0x260003e01ff807fe 0x64c0007c03ff00ff

def z762 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0xffffcc001fffffc5 0xfffff98003fffff8

def z763 : W := mkw 0xdff7afd6d4000002 0x1bfef5fada800000 0xdffffffffe000001 0xfbffffffffc00000

def z764 : W := mkw 0x200850293ffefff8 0x64010a0527ffdfff 0x200000001ffffffe 0x2400000003ffffff

def z765 : W := mkw 0x0226815240000000 0x0044d02a48000000 0xd67ff3ffe0000001 0xdacffe7ffc000000

def z766 : W := mkw 0x022440000090b000 0x0044880000121600 0xb7e7c00019fff801 0xf6fcf800033fff00

def z767 : W := mkw 0x5858280db6074340 0x8b0b0501b6c0e868 0xd8783c1fe607c1c5 0x9b0f0783fcc0f838

def z768 : W := mkw 0xc7f787d6c0000002 0x18fef0fad8000000 0xd7fff3ffe0000001 0xdafffe7ffc000000

def z769 : W := mkw 0xc27f415fa297fa49 0xb84fe82bf452ff49 0x807fc01fe007f800 0x100ff803fc00ff00

def z770 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x378033e01ff807fe 0xe6f0067c03ff00ff

def z771 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0xf8783f1ffe07c7ff 0xff0f07e3ffc0f8ff

def z772 : W := mkw 0x1fa62fdb15aaeb98 0x63f4c5fb62b55d73 0x89e60c1f063ff9c4 0x113cc183e0c7ff38

def z773 : W := mkw 0x200850292a5e5ef8 0x24010a05254bcbdf 0x20000000063e3ffe 0x2400000000c7c7ff

def z774 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0x366633e719c7fe3a 0xe6ccc67ce338ffc7

def z775 : W := mkw 0x1d0038201d600520 0x03a0070403ac00a4 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z776 : W := mkw 0xdff7afd6d5a1a003 0x1bfef5fadab43400 0xfffffffffff9c001 0xffffffffffff3800

def z777 : W := mkw 0xdaf7afd6c0000002 0x1b5ef5fad8000000 0xd87fffffe0000001 0x9b0ffffffc000000

def z778 : W := mkw 0x22a6877240c8a8b8 0x2454d0ee48191517 0x260603e001c0383a 0x44c0c07c00380707

def z779 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0xfffff3e01ffff801 0xfffffe7c03ffff00

def z780 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0xffffffffe0063801 0xfffffffffc00c700

def z781 : W := mkw 0x5dd2af94c0000000 0x0bba55f298000000 0xdfffffffe0000001 0xdbfffffffc000000

def z782 : W := mkw 0x1f2c400017b4b000 0x03e5880002f69600 0xbfffc0001ffff801 0xf7fff80003ffff00

def z783 : W := mkw 0x4058000da2074240 0x880b0001b440e848 0x88780c1fe607c1c4 0x110f0183fcc0f838

def z784 : W := mkw 0x200850292ad6fe68 0x24010a05255adfcd 0x2000000019c7fe3a 0x240000000338ffc7

def z785 : W := mkw 0x78d2ff15dc195d98 0x8f1a5fe2bb832bb3 0x31e7f3071839f83a 0xc63cfe60e3073f07

def z786 : W := mkw 0xdff7afd6c1a0a003 0x1bfef5fad8341400 0xdfffffffe1c00001 0xdbfffffffc380000

def z787 : W := mkw 0xda77a956c0000002 0x1b4ef52ad8000000 0xde7fffffe0000001 0xdbcffffffc000000

def z788 : W := mkw 0xdf7d68c697b5b003 0x1befad18d2f6b600 0xfffffcfffffff801 0xffffff9fffffff00

def z789 : W := mkw 0x5858280db6074340 0x8b0b0501b6c0e868 0xc8780c1fe607c7c5 0x390f0183fcc0f8f8

def z790 : W := mkw 0x6082bfffe84a4efa 0x2c1057fffd0949df 0x40003fffe00007fe 0x080007fffc0000ff

def z791 : W := mkw 0x2082977b484a4eb8 0x241052ef690949d7 0x400033ff0000063a 0x0800067fe00000c7

def z792 : W := mkw 0x5858382dbe474760 0x8b0b0705b7c8e8ec 0xde783cffffc7c7c5 0xbbcf079ffff8f8f8

def z793 : W := mkw 0x18803e201c4805b0 0x031007c4038900b6 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z794 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0x5ff9ffffe0000000 0x8bff3ffffc000000

def z795 : W := mkw 0xdd59780dbf375741 0x9bab2f01b7e6eae8 0xf9fffc1ffe3fffc5 0xff3fff83ffc7fff8

def z796 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0x699fcf18e6383ffe 0x4d33f9e31cc707ff

def z797 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0xdffffffff807c001 0xfbffffffff00f800

def z798 : W := mkw 0x5858382dbe474f68 0xab0b0705b7c8e9ed 0xd8783c1ffe07c7ff 0xbb0f0783ffc0f8ff

def z799 : W := mkw 0xdff7afd6c0080092 0x1bfef5fad8010012 0xffffffffe038003b 0xdffffffffc070007

def z800 : W := mkw 0x008ac710421c1090 0x001158e208438212 0xe99fcf18e63e3fff 0x7d33f9e31cc7c7ff

def z801 : W := mkw 0x00001020084804b0 0x0000020401090096 0x760033e01ff807ff 0xeec0067c03ff00ff

def z802 : W := mkw 0x00800620004800b0 0x001000c400090016 0x6f800fe007f807ff 0x6df001fc00ff00ff

def z803 : W := mkw 0x1d8006a0156800b0 0x43b000d402ad0016 0x7f800fe01ff807ff 0xeff001fc03ff00ff

def z804 : W := mkw 0x1d802ea0016800b0 0x43b005d4002d0016 0x7f803fe007f807ff 0xeff007fc00ff00ff

def z805 : W := mkw 0x5af6af56c0000000 0x0b5ed5ead8000000 0xdfffffffe0000001 0xdbfffffffc000000

def z806 : W := mkw 0x000810093e074740 0x8001020127c0e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z807 : W := mkw 0x058016a01d6805b0 0x40b002d403ad00b6 0x778033e01ff807ff 0xeef0067c03ff00ff

def z808 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0xd9fffc1ffe07c7c5 0xfb3fff83ffc0f8f8

def z809 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0xc9ffffffe0000000 0x193ffffffc000000

def z810 : W := mkw 0xdff7afd6d5a1a003 0x1bfef5fadab43400 0xfffffffff9c7f801 0xffffffffff38ff00

def z811 : W := mkw 0x58582804b6050140 0x8b0b050096c0a028 0xd8783c1ffe07c1c5 0xbb0f0783ffc0f838

def z812 : W := mkw 0x872d400003b4b001 0x10e5a80000769600 0xbfffc0001ffff801 0xf7fff80003ffff00

def z813 : W := mkw 0x5858380dbf274740 0x8b0b0701b7e4e8e8 0xf8783c1fffffc7c5 0xbf0f0783fffff8f8

def z814 : W := mkw 0xddd1bea4dd6805b2 0x5bba37d49bad00b6 0xfff9fffffff807ff 0xffff3fffffff00ff

def z815 : W := mkw 0xc7a7afd6c0000002 0x18f4f5fad8000000 0xcf9fffffe0000001 0x59f3fffffc000000

def z816 : W := mkw 0x00828718400a0a98 0x001050e308014153 0xe99fcf18e63e3fff 0x7d33f9e31cc7c7ff

def z817 : W := mkw 0x87a787d240000002 0x10f4f0fa48000000 0xdfffffffe0000001 0xdbfffffffc000000

def z818 : W := mkw 0xdf7d6804b7b5b141 0x9befad0096f6b628 0xfffffc1ffffff9c5 0xffffff83ffffff38

def z819 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0x98783c1ffe07c1c4 0x930f0783ffc0f838

def z820 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0xf9ffff1fe63e3fff 0xff3fffe3fcc7c7ff

def z821 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0x2f9fc0001ffff800 0x65f3f80003ffff00

def z822 : W := mkw 0x5dd03ea59d6945b0 0xcbba07d4b3ad28b6 0xfff83ffffff9c7ff 0xffff07ffffff38ff

def z823 : W := mkw 0xa7a7c7f240d8b8ba 0x34f4f8fe481b1717 0x2787c3e001f8383a 0x44f0f87c003f0707

def z824 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0xff983ff8fff807ff 0xfff307ff1fff00ff

def z825 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0xc8783c1fe607c7c4 0x190f0783fcc0f8f8

def z826 : W := mkw 0x222ec15a6296ba48 0x2445d82b4c52d749 0x801fc018e0063800 0x1003f8031c00c700

def z827 : W := mkw 0x0224102908c2e620 0x0044820521185cc4 0xf66633ff19c7fe3b 0xfeccc67fe338ffc7

def z828 : W := mkw 0x1d803ea11d6945b0 0xc3b007d423ad28b6 0x7f803fe01ff9c7ff 0xeff007fc03ff38ff

def z829 : W := mkw 0xff7d68cea21e1ada 0x1fefad19d443c35b 0x366030e7063e3ffe 0xa6cc061ce0c7c7ff

def z830 : W := mkw 0xdf7d680497b5b001 0x1befad0092f6b600 0xbfffcc00fffff801 0xf7fff9801fffff00

def z831 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0xd67fffffe0000000 0x9acffffffc000000

def z832 : W := mkw 0x0226017200c0a828 0x2044c02e40181505 0xf66633ff19c7f83b 0xfeccc67fe338ff07

def z833 : W := mkw 0x9dd13ea01d6905b1 0x53ba27d403ad20b6 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z834 : W := mkw 0x4058100dbe074740 0x880b0201b7c0e8e8 0xc8780c1ffe07c7c5 0x390f0183ffc0f8f8

def z835 : W := mkw 0x5850380dbc034740 0x8b0a0701b78068e8 0xd8783c1ff801c7c5 0x9b0f0783ff0038f8

def z836 : W := mkw 0x4058000da2074240 0x880b0001b440e848 0xc0780c1fe007c7c4 0x180f0183fc00f8f8

def z837 : W := mkw 0x5800380dbc024740 0x8b000701b78048e8 0xd8603c1ffe07c7c5 0xbb0c0783ffc0f8f8

def z838 : W := mkw 0x5a7e2976b6c5a968 0xab4fc52ed6d8b52d 0x2e1e0fe0e7c039fe 0x45c3c1fc1cf8073f

def z839 : W := mkw 0x5dd03ea49d6805b0 0x4bba07d493ad00b6 0x7f983fe0fff807ff 0xeff307fc1fff00ff

def z840 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0xffe633ff1ffffe3b 0xfffcc67fe3ffffc7

def z841 : W := mkw 0xdff7afd6c081a003 0x1bfef5fad8103400 0xdfffffffe001c001 0xdbfffffffc003800

def z842 : W := mkw 0xdf7d4004b7b5b041 0x9befa80096f6b608 0xbfffc000fffff801 0xf7fff8001fffff00

def z843 : W := mkw 0xdd59380dbf274741 0x9bab2701b7e4e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z844 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0xc99fcf18e63e3ffe 0x1933f9e31cc7c7ff

def z845 : W := mkw 0xa27fc15b6297fa49 0x344ff82b6c52ff49 0x807fc01fe007f800 0x100ff803fc00ff00

def z846 : W := mkw 0xdf7538e69de1a523 0x5beea71cd3bc34a4 0x166030e719c1c000 0x82cc061ce3383800

def z847 : W := mkw 0x9f25400015b0b001 0x13e4a80002b61600 0xbfe7c0001ffff801 0xf7fcf80003ffff00

def z848 : W := mkw 0x827d40000295b001 0x104fa8000052b600 0xbfffc0001ffff801 0xf7fff80003ffff00

def z849 : W := mkw 0xc2778156c0000002 0x184ef02ad8000000 0x967ff0ffe0000000 0x92cffe1ffc000000

def z850 : W := mkw 0x872d400017b5b001 0x10e5a80002f6b600 0xb7e7c0001ffff801 0xf6fcf80003ffff00

def z851 : W := mkw 0x827d400017b5b001 0x104fa80002f6b600 0xa9ffc0001ffff801 0x753ff80003ffff00

def z852 : W := mkw 0x8227917b48c2ee2a 0x3044f22f69185dc5 0xf667f3ff19c7fe3b 0xfeccfe7fe338ffc7

def z853 : W := mkw 0x0226015a0082aa08 0x0044c02b40105541 0xf66633ff19c7fe3b 0xfeccc67fe338ffc7

def z854 : W := mkw 0x27a6c7f241f8b8b8 0x64f4d8fe483f1717 0x2787c3e001f8383a 0x44f0f87c003f0707

def z855 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x6f803fe007f807fe 0x4df007fc00ff00ff

def z856 : W := mkw 0x00884608221e12d0 0x001108c10443c25a 0xe99fcf18e63e3fff 0x7d33f9e31cc7c7ff

def z857 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0x37e7c0001ffff800 0xe6fcf80003ffff00

def z858 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x76003fe01ff807fe 0xaec007fc03ff00ff

def z859 : W := mkw 0x0000100928024640 0x00000201250048c8 0xd0603c1ff807c7c5 0xba0c0783ff00f8f8

def z860 : W := mkw 0xdd59780dbf375741 0x9bab2f01b7e6eae8 0xfff9fc1fffffc7c5 0xffff3f83fffff8f8

def z861 : W := mkw 0xc2f78756c0000002 0x185ef0ead8000000 0xdfffffffe0000001 0xdbfffffffc000000

def z862 : W := mkw 0x9f7d680017b5b101 0x13efad0002f6b620 0xbfffcc001ffff9c5 0xf7fff98003ffff38

def z863 : W := mkw 0x2088c608621e1ad8 0x041118c10c43c35b 0xa99fcc00e63e3fff 0x7533f9801cc7c7ff

def z864 : W := mkw 0x5850380da8024740 0x8b0a0701b50048e8 0xd8783c1ff807c7c5 0xbb0f0783ff00f8f8

def z865 : W := mkw 0x200850293f7f5ff8 0xc4010a0527efebff 0x200000001ffffffe 0x2400000003ffffff

def z866 : W := mkw 0x20084008221e1ad8 0x040108010443c35b 0xe99fcc18e63e3fff 0x7d33f9831cc7c7ff

def z867 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0xffe03fe01fffc7ff 0xfffc07fc03fff8ff

def z868 : W := mkw 0xdf77a9d6c0000002 0x1beef53ad8000000 0x9ffff0ffe0000001 0xd3fffe1ffc000000

def z869 : W := mkw 0xdff5aec6c0000002 0x1bfeb5d8d8000000 0xdff9fcffe0000001 0x9bff3f9ffc000000

def z870 : W := mkw 0x6082bfbde84a4ff8 0xcc1057f7bd0949ff 0x40003fffe00007fe 0x080007fffc0000ff

def z871 : W := mkw 0x1d08400017b5b001 0x03a1080002f6b600 0xbf9fc0001ffff801 0xf7f3f80003ffff00

def z872 : W := mkw 0x0008400017b5b001 0x0001080002f6b600 0x2187c0001ffff800 0x6430f80003ffff00

def z873 : W := mkw 0x05803ea0096805b0 0x40b007d4012d00b6 0x6f803fe007f807ff 0x6df007fc00ff00ff

def z874 : W := mkw 0x5d803ea59d6845b0 0xcbb007d4b3ad08b6 0x7f803fe71ff807ff 0xeff007fce3ff00ff

def z875 : W := mkw 0x058016a01d6805b0 0x40b002d403ad00b6 0x6f800fe01ff807ff 0x6df001fc03ff00ff

def z876 : W := mkw 0xc725780da9b2f741 0x98e4af01b5365ee8 0x6787fc1fe1f83fc4 0x4cf0ff83fc3f07f8

def z877 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0xffffffffe000063b 0xfffffffffc0000c7

def z878 : W := mkw 0xddd3afd6c0000002 0x1bba75fad8000000 0x5f99ffffe0000001 0xcbf33ffffc000000

def z879 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0xfe7e3ffff9c7fe3b 0xffcfc7ffff38ffc7

def z880 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0xff9fcf18fffe3fff 0xfff3f9e31fffc7ff

def z881 : W := mkw 0x4058100daa074640 0x880b0201b540e8c8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z882 : W := mkw 0x4058280da2074340 0x880b0501b440e868 0x80780c1fe007c1c4 0x100f0183fc00f838

def z883 : W := mkw 0x5d82afd6c0000002 0x0bb055fad8000000 0xdf9fffffe0000001 0xdbf3fffffc000000

def z884 : W := mkw 0x22acd6636adcf4f0 0x24559acc6d5b9e9e 0x1ff9fce7fff9c1c4 0x83ff3f9cffff3838

def z885 : W := mkw 0xdff7afd6c080a80a 0x3bfef5fad8101501 0xdfffffffe0003801 0xdbfffffffc000700

def z886 : W := mkw 0x9f7d688017b5b101 0x53efad1002f6b620 0xbfffc0001ffff801 0xf7fff80003ffff00

def z887 : W := mkw 0xe27fc15ee297ba4b 0x1c4ff82bdc52f749 0x807fc01fe007f800 0x100ff803fc00ff00

def z888 : W := mkw 0x4082bfffc84a4fba 0x681057fff90949f7 0x40003fffe00007fe 0x080007fffc0000ff

def z889 : W := mkw 0x208ac710621c18d8 0x041158e20c43831b 0x699fcf00e6383fff 0x6d33f9e01cc707ff

def z890 : W := mkw 0x5d58388dbf274740 0xcbab0711b7e4e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z891 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0xd0783c1ff807c7c4 0x9a0f0783ff00f8f8

def z892 : W := mkw 0x5d58380dbf274740 0x8bab0701b7e4e8e8 0xde783c1fffc7c7c5 0xbbcf0783fff8f8f8

def z893 : W := mkw 0x0226117208c0a420 0x0044c22e41181484 0xf66633ff19c7fe3b 0xfeccc67fe338ffc7

def z894 : W := mkw 0x1858400017b5b001 0x030b080002f6b600 0xb9ffc0001ffff801 0xf73ff80003ffff00

def z895 : W := mkw 0xddd3afd6c0000002 0x1bba75fad8000000 0xc99fffffe0000001 0x5933fffffc000000

def z896 : W := mkw 0xdf7538679de1e521 0xbbeea70cf3bc3ca4 0x166030e719c1c000 0x82cc061ce3383800

def z897 : W := mkw 0x000850293ff7ff69 0xa0010a0527feffed 0x200000001ffffffe 0x2400000003ffffff

def z898 : W := mkw 0x208ac719621e5ad8 0x041158e32c43cb5b 0xe9ffcf1fe63fffff 0x7d3ff9e3fcc7ffff

def z899 : W := mkw 0x6082bf7fe84a4ff8 0xac1057effd0949ff 0x40003fffe00007fe 0x080007fffc0000ff

def z900 : W := mkw 0xa7a7c77241f8b8b9 0x34f4f8ee483f1717 0x2787c3e001f8383a 0x44f0f87c003f0707

def z901 : W := mkw 0x5858280cb6070240 0x0b0b050196c0e048 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z902 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0xfffffffff9c00001 0xffffffffff380000

def z903 : W := mkw 0x1d8016201d6804b0 0x03b002c403ad0096 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z904 : W := mkw 0x5858780dbe175740 0x8b0b0f01b7c2eae8 0xd9f9fc1ffe3fc7c5 0xbb3f3f83ffc7f8f8

def z905 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0xf9ffcf18fe3fffff 0xff3ff9e31fc7ffff

def z906 : W := mkw 0xdff52e8480000000 0x1bfea5d090000000 0xdfffffffe0000001 0xdbfffffffc000000

def z907 : W := mkw 0x58d2afd6c0000002 0x0b1a55fad8000000 0xd9ffffffe0000001 0xdb3ffffffc000000

def z908 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0xa99fcc18e63e3ffe 0x3533f9831cc7c7ff

def z909 : W := mkw 0x008016201d6805b0 0x401002c403ad00b6 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z910 : W := mkw 0xdf77295680000000 0x1beee52ad0000000 0xdfffffffe0000001 0xdbfffffffc000000

def z911 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0xfe663fff1fc7ffff 0xffccc7ffe3f8ffff

def z912 : W := mkw 0x0226117b28c2ef68 0xa044c22f65185ded 0xf66633ff19c7ffff 0xfeccc67fe338ffff

def z913 : W := mkw 0xc0d3afd6c0000002 0x181a75fad8000000 0x4019ffffe0000000 0x08033ffffc000000

def z914 : W := mkw 0x4058380daa074740 0x880b0701b540e8e8 0xc8783c1fe607c7c5 0x390f0783fcc0f8f8

def z915 : W := mkw 0xc2f7afd6c0000002 0x185ef5fad8000000 0xc9ffffffe0000001 0x593ffffffc000000

def z916 : W := mkw 0xdff7afd6c080a002 0x1bfef5fad8101400 0xdfffffffe007f801 0xdbfffffffc00ff00

def z917 : W := mkw 0x5858000db6074240 0x8b0b0001b6c0e848 0xd8780c1ffe07c7c5 0xbb0f0183ffc0f8f8

def z918 : W := mkw 0x058006a0016800b0 0x40b000d4002d0016 0x278003e007f807fe 0x64f0007c00ff00ff

def z919 : W := mkw 0x5858382dbe474760 0x8b0b0705b7c8e8ec 0xf8783c1fffc7c7ff 0xbf0f0783fff8f8ff

def z920 : W := mkw 0x1d803ea0084804b0 0x03b007d401090096 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z921 : W := mkw 0x585038059c014500 0x8b0a0700b38028a0 0xd8783c1ffe01c7c5 0xbb0f0783ffc038f8

def z922 : W := mkw 0x1d802e8015280090 0x03b005d002a50012 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z923 : W := mkw 0x5d5838adbf674760 0xcbab0715b7ece8ec 0xfff83cffffffc7c5 0xffff079ffffff8f8

def z924 : W := mkw 0xa7a7c7d241b8b89b 0x14f4f8fa48371713 0x2787c3e001f8383a 0x44f0f87c003f0707

def z925 : W := mkw 0x2082bffb684a4ff8 0x641057ff6d0949ff 0x40003fffe00007fe 0x080007fffc0000ff

def z926 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0xdfffffffe60007c5 0xfbfffffffcc000f8

def z927 : W := mkw 0x0002113908424e28 0x00004227210849c5 0xf66633ff19c7fe3b 0xfeccc67fe338ffc7

def z928 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0x50603c1ffe07c7c4 0xaa0c0783ffc0f8f8

def z929 : W := mkw 0x208ac718621e1ad8 0x041158e30c43c35b 0xff9ffff8e63e3fff 0xfff3ffff1cc7c7ff

def z930 : W := mkw 0x4000380da8024740 0x88000701b50048e8 0xc0603c1fe007c7c4 0x180c0783fc00f8f8

def z931 : W := mkw 0xc2f7afd6c0000002 0x185ef5fad8000000 0xd67fffffe0000001 0xdacffffffc000000

def z932 : W := mkw 0xdf77a9d6c0000002 0x1beef53ad8000000 0xde7ffcffe0000001 0x9bcfff9ffc000000

def z933 : W := mkw 0x585838049e050500 0x0b0b070093c0a0a0 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z934 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0xf87e3c1ffe07ffc5 0xff0fc783ffc0fff8

def z935 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0xffffcc18fffff801 0xfffff9831fffff00

def z936 : W := mkw 0x9f7d40000294b000 0x13efa80000529600 0xbfffc0001ffff801 0xf7fff80003ffff00

def z937 : W := mkw 0x4082afd6c0000002 0x081055fad8000000 0xc01fffffe0000000 0x1803fffffc000000

def z938 : W := mkw 0x05803ea01d6805b0 0x40b007d403ad00b6 0x67803fe01ff807fe 0x6cf007fc03ff00ff

def z939 : W := mkw 0xe27fc15fe296fa4a 0x3c4ff82bfc52df49 0x807fc01fe007f800 0x100ff803fc00ff00

def z940 : W := mkw 0xdd59388dbe074742 0x9bab2711b7c0e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z941 : W := mkw 0x4008380dbe074740 0x88010701b7c0e8e8 0xd0603c1ffe07c7c5 0xba0c0783ffc0f8f8

def z942 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0x4f9fffffe0000000 0x49f3fffffc000000

def z943 : W := mkw 0x5858780dbf375741 0x8b0b0f01b7e6eae8 0xd8783c1ffe3fc7c5 0xbb0f0783ffc7f8f8

def z944 : W := mkw 0x5858280db6074340 0x8b0b0501b6c0e868 0x98780c1ffe07c1c5 0xb30f0183ffc0f838

def z945 : W := mkw 0x5850380dbc034740 0x8b0a0701b78068e8 0xd0603c1ff807c7c5 0xba0c0783ff00f8f8

def z946 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0xf9f83c1ffe3fc7c5 0xff3f0783ffc7f8f8

def z947 : W := mkw 0xdff7afd6d4010002 0x1bfef5fada802000 0xdffffffff801c001 0xdbffffffff003800

def z948 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0xfffff3ff19c7fe3b 0xfffffe7fe338ffc7

def z949 : W := mkw 0xdff7afd6c000080a 0x1bfef5fad8000101 0xffffffffe000383b 0xdffffffffc000707

def z950 : W := mkw 0xdff7afd6c0080192 0x5bfef5fad8010032 0xdfffffffe00001c5 0xdbfffffffc000038

def z951 : W := mkw 0x185810093e074640 0x030b020127c0e8c8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z952 : W := mkw 0x585838adbe474760 0xcb0b0715b7c8e8ec 0xd8783cfffe07c7c5 0xbb0f079fffc0f8f8

def z953 : W := mkw 0x0226117308c0ec28 0x2044c22e61181d85 0xb66633e719c7f83b 0xf6ccc67ce338ff07

def z954 : W := mkw 0x180838093e064740 0x0301070127c0c8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z955 : W := mkw 0x5d58380dbf274740 0x8bab0701b7e4e8e8 0xd9f83c1ffe3fc7c5 0xbb3f0783ffc7f8f8

def z956 : W := mkw 0x9d59400017b5b001 0x13ab280002f6b600 0xa99fc0001ffff801 0x7533f80003ffff00

def z957 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0xb7ffc00019fff800 0xd6fff800033fff00

def z958 : W := mkw 0x208ac719621f5ad8 0x841158e32c43eb5b 0xe99fcf18e63fffff 0x7d33f9e31cc7ffff

def z959 : W := mkw 0x4058380daa074740 0x880b0701b540e8e8 0xd0783c1ff807c7c5 0xba0f0783ff00f8f8

def z960 : W := mkw 0xdf7d688497b5b003 0x1befad1092f6b600 0xbfffc0001ffff801 0xf7fff80003ffff00

def z961 : W := mkw 0x1d802ea0156801b0 0x43b005d402ad0036 0x6f800fe007f807ff 0x6df001fc00ff00ff

def z962 : W := mkw 0xdf7d404697b5b003 0x1befa808d2f6b600 0xbfffc0071ffff801 0xf7fff800e3ffff00

def z963 : W := mkw 0x2082c71040181898 0x041058e208030313 0xe99fcf18e6383fff 0x7d33f9e31cc707ff

def z964 : W := mkw 0x1dd03ea01d6905b0 0x43ba07d403ad20b6 0x7fe03fe01ff9c7ff 0xeffc07fc03ff38ff

def z965 : W := mkw 0x200850293ffffef9 0x24010a0527ffffdf 0x200000001ffffffe 0x2400000003ffffff

def z966 : W := mkw 0x5858380daa064640 0x0b0b0701b540c8c8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z967 : W := mkw 0x1d803ea11d6845b0 0x43b007d423ad08b6 0x7fe03fe71ff9c7ff 0xeffc07fce3ff38ff

def z968 : W := mkw 0x1fa6afd240000000 0x03f4d5fa48000000 0xdfffffffe0000001 0xdbfffffffc000000

def z969 : W := mkw 0x5858380dbe074f48 0x8b0b0701b7c0e9e9 0xf8783c1ffe07ffff 0xbf0f0783ffc0ffff

def z970 : W := mkw 0xc7f7afd6c0000002 0x18fef5fad8000000 0xc7ffffffe0000000 0x58fffffffc000000

def z971 : W := mkw 0xdf7d400497b5b001 0x1befa80092f6b600 0xbfffc01ffffff801 0xf7fff803ffffff00

def z972 : W := mkw 0x5d803ea49d6805b0 0x4bb007d493ad00b6 0x7f803ffffff807ff 0xeff007ffffff00ff

def z973 : W := mkw 0xdf778156c0000002 0x1beef02ad8000000 0xdffff3ffe0000001 0xdbfffe7ffc000000

def z974 : W := mkw 0x4082afd6c0000002 0x081055fad8000000 0x4999ffffe0000000 0x09333ffffc000000

def z975 : W := mkw 0x877d400017b5b001 0x10efa80002f6b600 0xa7ffc0001ffff800 0x74fff80003ffff00

def z976 : W := mkw 0x000850293ffff7f1 0xc0010a0527fffefe 0x200000001ffffffe 0x2400000003ffffff

def z977 : W := mkw 0xfdd9ee84f73d10d3 0x1fbb3dd09ee7a21a 0x0999cc00e63801c4 0x013339801cc70038

def z978 : W := mkw 0xdff7afd6d4010102 0x9bfef5fada802020 0xdfffffffe0000001 0xdbfffffffc000000

def z979 : W := mkw 0x9ff7875240000000 0x13fef0ea48000000 0xdfffffffe0000001 0xdbfffffffc000000

def z980 : W := mkw 0x4050380da8034740 0x880a0701b50068e8 0x40603c1fe001c7c4 0x080c0783fc0038f8

def z981 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x5f803fe01ff807fe 0x8bf007fc03ff00ff

def z982 : W := mkw 0xdff7afd6c0080092 0x1bfef5fad8010012 0xdfffffffe00007ff 0xdbfffffffc0000ff

def z983 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0x58783c1ffe01c7c4 0x8b0f0783ffc038f8

def z984 : W := mkw 0x000840000294b000 0x0001080000529600 0xa99fc0001ffff801 0x7533f80003ffff00

def z985 : W := mkw 0x9f7d400037b5b041 0x13efa80006f6b608 0xbfffcc00fffff9c5 0xf7fff9801fffff38

def z986 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0xfffff01f1ffff801 0xfffffe03e3ffff00

def z987 : W := mkw 0x1d0010201d6805b0 0x43a0020403ad00b6 0x7f8033e01ff807ff 0xeff0067c03ff00ff

def z988 : W := mkw 0x222e415b2296fa48 0x2445c82b6452df49 0x8066001f0007f800 0x100cc003e000ff00

def z989 : W := mkw 0x1a7c40001695b000 0x034f880002d2b600 0xbfffc0001ffff801 0xf7fff80003ffff00

def z990 : W := mkw 0x5d80bea4dd6805b2 0x4bb017d49bad00b6 0x7f803fe0fff807ff 0xeff007fc1fff00ff

def z991 : W := mkw 0x7dd8ee84f73d11d0 0xcfbb1dd09ee7a23a 0x0999cc00e63801c4 0x013339801cc70038

def z992 : W := mkw 0x5858280da2074240 0x8b0b0501b440e848 0xd8783c1fe607c7c5 0xbb0f0783fcc0f8f8

def z993 : W := mkw 0xddd96e84b73d11d1 0xdbbb2dd096e7a23a 0x0999cc00e63801c4 0x013339801cc70038

def z994 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0xde783ffffe07c7c5 0xfbcf07ffffc0f8f8

def z995 : W := mkw 0x2226917b68c2ee68 0x2444d22f6d185dcd 0xf66633fff9c7fe3b 0xfeccc67fff38ffc7

def z996 : W := mkw 0xdf7538e79de0e522 0x7beea71cf3bc1ca4 0x166030e719c1c000 0x82cc061ce3383800

def z997 : W := mkw 0x5850380d9c024700 0x0b0a0701b38048e0 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z998 : W := mkw 0xdff7afd6d5200102 0x5bfef5fadaa40020 0xdfffffffe0000001 0xdbfffffffc000000

def z999 : W := mkw 0xdff7afd6c0000002 0x1bfef5fad8000000 0x9ffffcffe0000000 0x93ffff9ffc000000

def z1000 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0xa9ffc0001ffff800 0x353ff80003ffff00

def z1001 : W := mkw 0x5d58382dbf674760 0x8bab0705b7ece8ec 0xfff83fffffffc7ff 0xffff07fffffff8ff

def z1002 : W := mkw 0x5858382dbf674760 0xcb0b0705b7ece8ec 0xd8783c1fffc7c7c5 0xbb0f0783fff8f8f8

def z1003 : W := mkw 0x9f7d40c217b5b003 0x13efa81842f6b600 0xbfffc0e01ffff801 0xf7fff81c03ffff00

def z1004 : W := mkw 0x1d58400017351000 0x03ab080002e6a200 0xbfffc0001ffff801 0xf7fff80003ffff00

def z1005 : W := mkw 0x872d400017b5b001 0x10e5a80002f6b600 0xaf9fc0001ffff801 0x75f3f80003ffff00

def z1006 : W := mkw 0x208ac7da621e1ada 0x041158fb4c43c35b 0xe99fcff8e63e3fff 0x7d33f9ff1cc7c7ff

def z1007 : W := mkw 0x5858380dbe074740 0x8b0b0701b7c0e8e8 0x88780c1ffe07c7c4 0x310f0183ffc0f8f8

def z1008 : W := mkw 0x87a787f241e8a8ba 0x70f4f0fe483d1517 0x2787c3e001f8383a 0x44f0f87c003f0707

def z1009 : W := mkw 0xdff7afd6d5a0a002 0x1bfef5fadab41400 0xfffffffffffff801 0xffffffffffffff00

def z1010 : W := mkw 0x627ec15fe297fa48 0xac4fd82bfc52ff49 0x807fc01fe007f800 0x100ff803fc00ff00

def z1011 : W := mkw 0xc2778156c0000002 0x184ef02ad8000000 0xc07ff3ffe0000000 0x180ffe7ffc000000

def z1012 : W := mkw 0x9f75000015a0a000 0x13eea00002b41400 0xbfffc0001ffff801 0xf7fff80003ffff00

def z1013 : W := mkw 0x58583805be054540 0x8b0b0700b7c0a8a8 0xd8783c1ffe01c1c5 0x9b0f0783ffc03838

def z1014 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0x2f800fe01ff807fe 0x65f001fc03ff00ff

def z1015 : W := mkw 0xdf7528c680000002 0x1beea518d0000000 0xdffffcffe0000001 0xdbffff9ffc000000

def z1016 : W := mkw 0x4008380daa064740 0x88010701b540c8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z1017 : W := mkw 0x5d58780dbf375740 0x8bab0f01b7e6eae8 0xfffffc1fffffffc5 0xffffff83fffffff8

def z1018 : W := mkw 0x5d58388dbe074740 0x8bab0711b7c0e8e8 0xde783cfffe07c7c5 0xbbcf079fffc0f8f8

def z1019 : W := mkw 0xdff7afd6c0080092 0x1bfef5fad8010012 0xdfffffffe63801c5 0xdbfffffffcc70038

def z1020 : W := mkw 0x022c400017b5b001 0x0045880002f6b600 0xbfffc0001ffff801 0xf7fff80003ffff00

def z1021 : W := mkw 0xdff7afd6d5280192 0x5bfef5fadaa50032 0xffffffffe63807ff 0xfffffffffcc700ff

def z1022 : W := mkw 0xdff7afd6c080a002 0x1bfef5fad8101400 0xffffffffe1c03801 0xdffffffffc380700

def z1023 : W := mkw 0xdf7538a59de1e521 0xdbeea714b3bc3ca4 0x166030e719c1c000 0x82cc061ce3383800

def z1024 : W := mkw 0x5d58380dbe074740 0x8bab0701b7c0e8e8 0xdff83c1ffe07c7c5 0xfbff0783ffc0f8f8

def z1025 : W := mkw 0x5dd03ea49d6905b0 0xcbba07d493ad20b6 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z1026 : W := mkw 0x1d803ea01d6805b0 0x43b007d403ad00b6 0xff9fffe01ff807ff 0xfff3fffc03ff00ff

def z1027 : W := mkw 0x9f7d400017b5b001 0x13efa80002f6b600 0xffffc3001ffffe3b 0xfffff86003ffffc7

def z1028 : W := mkw 0x9f7d680017b5b001 0x13efad0002f6b600 0xfffffc001ffff801 0xffffff8003ffff00

def z1029 : W := mkw 0x42a6afd6c0000002 0x0854d5fad8000000 0xdfffffffe0000001 0xdbfffffffc000000

def z1030 : W := mkw 0xdff7afd6c080a002 0x1bfef5fad8101400 0xdffffffff9c1c001 0xdbffffffff383800

def z1031 : W := mkw 0xdff7afd6c1200002 0x1bfef5fad8240000 0xffffffffe1f80001 0xdffffffffc3f0000

def z1032 : W := mkw 0x4058380dbe074740 0x880b0701b7c0e8e8 0xc0783c1ffe07c7c4 0x380f0783ffc0f8f8

def z1033 : W := mkw 0x5858780dbe175740 0x8b0b0f01b7c2eae8 0xf8783c1ffe3fffc5 0xbf0f0783ffc7fff8

def z1034 : W := mkw 0x5858382dbe474760 0x8b0b0705b7c8e8ec 0xd8783ffffe07c7ff 0xbb0f07ffffc0f8ff

def z1035 : W := mkw 0x2088c600621c10d0 0x041118c00c43821a 0xe99fcf00e63e3fff 0x7d33f9e01cc7c7ff

def z1036 : W := mkw 0x180038201d6805b0 0x4300070403ad00b6 0x7e003fe01ff807ff 0xefc007fc03ff00ff

def z1037 : W := mkw 0x208ac75a621e1ad8 0x041158eb4c43c35b 0xe99fffffe63e3fff 0x7d33fffffcc7c7ff

def z1038 : W := mkw 0x000a411822161a48 0x000148230442c349 0xe99fcf18e63e3fff 0x7d33f9e31cc7c7ff

def z1039 : W := mkw 0x9f7d400037b5b141 0x93efa80006f6b628 0xbfffc0001ffff9c5 0xf7fff80003ffff38

def z1040 : W := mkw 0xdf77a9d6c0000002 0x1beef53ad8000000 0xd67ff3ffe0000001 0xdacffe7ffc000000

def z1041 : W := mkw 0x200850293edffff8 0xa4010a0527dbffff 0x200000001ffffffe 0x2400000003ffffff

def z1042 : W := mkw 0x00803ea01d6805b0 0x401007d403ad00b6 0x76003fe01ff807ff 0xeec007fc03ff00ff

def z1043 : W := mkw 0x8725400001b0b001 0x10e4a80000361600 0x2787c00019fff800 0x64f0f800033fff00

def z1044 : W := mkw 0x00803ea0084805b0 0x401007d4010900b6 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z1045 : W := mkw 0xdff7afd6d5210003 0x1bfef5fadaa42000 0xdfffffffe0000001 0xdbfffffffc000000

def z1046 : W := mkw 0x0226117b08c2ee28 0x2044c22f61185dc5 0x766033ff19c7fe3a 0xaecc067fe338ffc7

def z1047 : W := mkw 0x1d8016a01d6805b0 0x43b002d403ad00b6 0x3f8003e01ff807ff 0xe7f0007c03ff00ff

def z1048 : W := mkw 0x877d400003b5b001 0x10efa8000076b600 0xb7ffc00019fff801 0xf6fff800033fff00

def z1049 : W := mkw 0x9f75400001b0b001 0x13eea80000361600 0xbfffc00019fff801 0xf7fff800033fff00

def z1050 : W := mkw 0x5850380dbc034740 0x8b0a0701b78068e8 0x58603c1ffe01c7c5 0xab0c0783ffc038f8

def z1051 : W := mkw 0x058016a0096804b0 0x40b002d4012d0096 0x7f803fe01ff807ff 0xeff007fc03ff00ff

def z1052 : W := mkw 0xdd59380dbe074740 0x9bab2701b7c0e8e8 0xd9f9fc1ffe07c7c5 0xbb3f3f83ffc0f8f8

def z1053 : W := mkw 0x22a6c7524098b898 0x2454d8ea48131713 0x2187c3000038383a 0x4430f86000070707

def z1054 : W := mkw 0xdff7afd6d5280192 0x5bfef5fadaa50032 0xfffffffffff801c5 0xffffffffffff0038

def z1055 : W := mkw 0xdff7afd6d5200002 0x1bfef5fadaa40000 0xdffffffff9c00001 0xdbffffffff380000

def z1056 : W := mkw 0x5858780dbe175740 0x8b0b0f01b7c2eae8 0xd87ffc1ffe07ffc5 0xbb0fff83ffc0fff8

def z1057 : W := mkw 0x0000102908c2ee28 0x2000020521185dc5 0xf66033ff19c7fe3b 0xfecc067fe338ffc7

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z7,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z9,z6])],[(0,[z10,z2,z3,z11,z5,z8,z6]),(0,[z2,z3,z12,z4,z5,z8,z6]),(0,[z2,z13,z14,z4,z5,z8,z6]),(0,[z2,z15,z3,z4,z5,z8,z16])],[(0,[z17,z2,z3,z4,z5,z8,z6]),(1,[z2,z3,z4,z18,z8,z6])],[(0,[z10,z19,z2,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z20,z8,z6]),(0,[z2,z3,z4,z5,z21,z8,z6])],[(0,[z22,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z23,z8,z6]),(0,[z24,z2,z3,z4,z5,z8,z6]),(0,[z25,z2,z3,z4,z5,z8,z6]),(0,[z26,z2,z3,z4,z5,z8,z6])],[(0,[z27,z2,z3,z4,z5,z8,z6]),(0,[z28,z2,z4,z29,z5,z8,z6]),(1,[z2,z3,z4,z8,z30,z6]),(0,[z2,z3,z4,z5,z8,z31,z6]),(0,[z2,z32,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z33,z5,z8,z6])],[(0,[z34,z2,z3,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z35,z4,z5,z8,z6]),(0,[z2,z3,z36,z4,z5,z8,z6])],[(0,[z37,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z38,z39])],[(0,[z40,z2,z3,z4,z5,z8,z6]),(0,[z41,z19,z2,z4,z5,z8,z6]),(0,[z2,z42,z3,z4,z29,z5,z6]),(0,[z2,z3,z4,z5,z43,z8,z6]),(1,[z41,z2,z4,z5,z8,z44]),(0,[z2,z3,z4,z5,z8,z45,z6])],[(0,[z46,z2,z3,z4,z5,z8,z6]),(0,[z3,z4,z5,z47,z8,z48,z6]),(0,[z2,z14,z4,z5,z49,z8,z6]),(0,[z50,z2,z3,z4,z5,z8,z51])],[(0,[z52,z2,z4,z5,z8,z6,z39]),(0,[z2,z53,z3,z4,z5,z8,z6]),(0,[z54,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z55,z8,z6]),(0,[z2,z3,z4,z56,z5,z8,z6])],[(0,[z2,z57,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z47,z8,z30,z6]),(0,[z2,z3,z58,z4,z59,z8,z6])],[(0,[z52,z2,z3,z4,z5,z8,z6]),(1,[z2,z3,z4,z60,z8,z6]),(0,[z52,z41,z2,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z61,z8,z6]),(0,[z2,z3,z4,z62,z5,z8,z6]),(0,[z2,z15,z3,z4,z63,z8,z6]),(0,[z2,z3,z4,z5,z8,z64,z6])],[(0,[z2,z3,z4,z5,z8,z6,z65]),(0,[z2,z3,z4,z5,z8,z66,z6]),(0,[z2,z3,z4,z5,z67,z8,z6]),(0,[z68,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z69,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z4,z5,z70,z8,z6]),(0,[z2,z3,z4,z71,z5,z8,z6]),(0,[z2,z72,z3,z4,z5,z8,z6]),(0,[z2,z73,z3,z4,z5,z8,z6])],[(1,[z2,z3,z4,z74,z8,z6]),(0,[z2,z3,z4,z5,z75,z8,z6]),(0,[z76,z2,z3,z4,z59,z8,z6]),(0,[z2,z3,z4,z5,z77,z8,z6]),(0,[z2,z3,z78,z4,z5,z8,z6])],[(0,[z2,z3,z4,z79,z5,z8,z6]),(0,[z80,z2,z3,z4,z5,z8,z6])],[(0,[z81,z2,z3,z4,z5,z8,z6]),(0,[z82,z2,z3,z4,z5,z8,z83]),(0,[z2,z84,z3,z4,z5,z8,z6]),(0,[z1,z2,z3,z4,z18,z8,z6]),(0,[z2,z3,z4,z85,z5,z8,z6]),(0,[z2,z3,z4,z86,z5,z8,z6]),(0,[z2,z3,z4,z87,z8,z6,z88])],[(0,[z1,z89,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z8,z90,z6]),(0,[z91,z2,z3,z4,z5,z8,z6]),(0,[z92,z2,z3,z4,z5,z8,z6]),(0,[z93,z2,z3,z4,z5,z8,z6])],[(0,[z94,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z95,z6]),(0,[z96,z2,z3,z4,z5,z8,z6]),(0,[z97,z2,z3,z4,z5,z8,z83])],[(0,[z98,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z99,z4,z5,z8,z6]),(0,[z2,z3,z4,z49,z8,z100,z6]),(0,[z2,z3,z4,z5,z8,z101,z6]),(0,[z2,z3,z102,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z103])],[(0,[z2,z3,z4,z5,z8,z104,z6]),(0,[z2,z3,z4,z5,z8,z105,z6])]],
   [[(0,[z89,z3,z4,z5,z8,z48,z6]),(0,[z2,z106,z3,z4,z5,z8,z6]),(0,[z2,z107,z4,z5,z8,z6,z39]),(0,[z2,z3,z4,z5,z8,z6,z108]),(0,[z2,z3,z4,z5,z109,z8,z51])],[(1,[z110,z2,z3,z4,z8,z6]),(0,[z111,z2,z3,z4,z112,z8,z6]),(0,[z2,z3,z4,z5,z8,z113,z6]),(0,[z50,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z114,z4,z5,z8,z115])],[(0,[z111,z2,z3,z58,z4,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z116]),(0,[z2,z3,z4,z117,z5,z8,z83]),(0,[z2,z3,z118,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z119,z6])],[(1,[z2,z15,z4,z5,z101,z6]),(0,[z2,z3,z4,z5,z8,z120,z6]),(0,[z121,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z109,z6,z51])],[(0,[z2,z3,z4,z5,z8,z6,z122]),(0,[z2,z123,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z124,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z6,z125]),(0,[z2,z3,z4,z5,z8,z126,z6]),(0,[z2,z3,z4,z5,z127,z8,z6])],[(0,[z128,z2,z3,z4,z5,z8,z6]),(1,[z2,z3,z4,z129,z8,z6]),(0,[z130,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z131,z5,z8,z6]),(0,[z2,z3,z4,z132,z5,z133,z6]),(0,[z2,z3,z4,z5,z134,z8,z6])]],
   [[(0,[z111,z3,z4,z135,z5,z8,z6]),(0,[z2,z136,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z137,z6]),(0,[z2,z3,z4,z138,z5,z139,z8]),(0,[z2,z3,z4,z5,z140,z8,z6])],[(0,[z2,z3,z141,z4,z5,z8,z6]),(0,[z2,z3,z142,z4,z5,z8,z6]),(0,[z2,z143,z3,z4,z5,z8,z6]),(0,[z0,z89,z3,z4,z5,z8,z6]),(0,[z97,z2,z3,z4,z5,z8,z44]),(0,[z144,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z6,z145]),(0,[z3,z4,z135,z5,z112,z8,z6]),(1,[z2,z3,z4,z63,z8,z6]),(0,[z146,z2,z4,z5,z147,z8,z6]),(0,[z2,z148,z3,z4,z5,z8,z6])],[(0,[z149,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z150]),(0,[z2,z151,z3,z4,z5,z8,z6]),(0,[z152,z2,z3,z4,z5,z8,z6])],[(0,[z153,z2,z3,z4,z5,z8,z6]),(1,[z2,z3,z4,z20,z8,z6])],[(0,[z19,z2,z154,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z155,z6]),(0,[z2,z3,z4,z5,z8,z6,z156]),(0,[z1,z2,z3,z157,z5,z8,z6])],[(1,[z2,z3,z4,z71,z8,z6]),(0,[z2,z3,z4,z158,z5,z8,z6]),(1,[z2,z3,z4,z5,z8,z159]),(0,[z2,z3,z4,z5,z49,z8,z6]),(0,[z2,z3,z4,z160,z5,z8,z6]),(0,[z76,z2,z3,z4,z161,z8,z6]),(0,[z2,z3,z114,z4,z5,z8,z38]),(0,[z162,z2,z3,z4,z5,z8,z6])],[(0,[z19,z2,z163,z4,z5,z8,z6]),(0,[z111,z2,z3,z4,z8,z100,z6]),(0,[z2,z3,z164,z4,z5,z8,z6]),(0,[z165,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z166,z8,z6])]],
   [[(1,[z82,z3,z4,z5,z8,z116]),(0,[z2,z3,z4,z5,z8,z167,z6]),(0,[z168,z2,z3,z4,z5,z8,z6]),(0,[z2,z169,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z170,z6]),(0,[z171,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z172,z4,z5,z8,z6]),(0,[z89,z2,z3,z4,z5,z48,z6]),(0,[z2,z173,z3,z4,z5,z174,z6])],[(0,[z2,z3,z175,z4,z5,z8,z6]),(0,[z82,z3,z4,z5,z8,z6,z116]),(1,[z2,z3,z114,z5,z8,z38]),(0,[z2,z3,z4,z5,z8,z6,z176]),(0,[z2,z3,z177,z4,z5,z8,z6])],[(0,[z178,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z179]),(0,[z180,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z59,z8,z100,z6])],[(0,[z181,z2,z3,z4,z5,z8,z6]),(0,[z10,z2,z4,z5,z49,z8,z6]),(0,[z2,z3,z4,z5,z174,z6,z51])],[(0,[z2,z3,z4,z5,z47,z8,z6]),(1,[z2,z3,z4,z5,z8,z182])],[(0,[z2,z3,z4,z5,z183,z8,z6]),(0,[z184,z2,z3,z4,z135,z8,z6]),(0,[z2,z3,z4,z161,z135,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z185]),(0,[z0,z2,z3,z4,z5,z47,z6]),(0,[z2,z14,z3,z4,z5,z8,z6]),(0,[z186,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z187,z8,z6]),(0,[z2,z188,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z189,z6]),(1,[z2,z4,z5,z8,z190,z6]),(0,[z2,z3,z4,z5,z8,z6,z191]),(0,[z192,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z193,z6]),(0,[z2,z3,z4,z5,z8,z194,z6]),(0,[z2,z3,z114,z4,z5,z8,z51])]],
   [[(0,[z2,z195,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z196,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z197,z6]),(0,[z2,z3,z141,z4,z29,z5,z8]),(1,[z2,z3,z4,z5,z155,z6]),(0,[z198,z2,z3,z4,z5,z8,z6]),(0,[z2,z173,z3,z4,z8,z100,z6])],[(0,[z111,z2,z3,z4,z199,z8,z6]),(0,[z41,z2,z4,z5,z49,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z200]),(0,[z2,z107,z3,z4,z5,z8,z44]),(0,[z201,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z100,z6,z51])],[(0,[z2,z3,z4,z5,z202,z8,z6]),(0,[z203,z2,z3,z4,z5,z8,z6])],[(1,[z2,z3,z4,z5,z170,z6]),(0,[z2,z3,z4,z5,z204,z8,z6])],[(0,[z2,z3,z4,z5,z205,z8,z6]),(0,[z2,z206,z3,z4,z5,z8,z6]),(0,[z207,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z208,z6]),(0,[z2,z3,z4,z5,z209,z8,z6]),(0,[z0,z2,z3,z157,z4,z5,z6]),(1,[z210,z2,z3,z4,z5,z6])],[(0,[z211,z2,z3,z4,z5,z8,z6]),(1,[z2,z3,z4,z5,z8,z191]),(0,[z2,z212,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z213,z5,z8,z6])]],
   [[(0,[z214,z2,z3,z4,z5,z8,z6]),(0,[z41,z2,z3,z4,z5,z8,z39]),(0,[z215,z2,z3,z4,z5,z8,z6]),(0,[z50,z2,z3,z4,z5,z8,z115]),(0,[z2,z3,z4,z132,z8,z6,z88])],[(0,[z19,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z216,z6]),(0,[z217,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z218,z5,z8,z6]),(0,[z2,z3,z157,z4,z5,z139,z6]),(0,[z2,z3,z4,z5,z8,z219,z6])],[(0,[z220,z3,z172,z4,z5,z8,z6]),(0,[z221,z2,z3,z4,z5,z8,z6]),(0,[z2,z222,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z6,z223]),(1,[z2,z3,z4,z5,z23,z6]),(0,[z224,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z225,z8,z100,z6]),(0,[z1,z2,z3,z4,z5,z137,z6]),(0,[z2,z173,z3,z4,z199,z8,z6])],[(0,[z2,z3,z4,z5,z226,z8,z6]),(0,[z227,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z83,z6]),(0,[z2,z3,z4,z5,z8,z228,z6])],[(0,[z229,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z117,z5,z8,z116]),(0,[z2,z3,z4,z5,z8,z44,z6]),(0,[z2,z3,z4,z199,z5,z100,z6])],[(0,[z2,z3,z4,z5,z230,z8,z6]),(0,[z231,z2,z3,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z4,z5,z232,z8,z6])],[(0,[z2,z3,z233,z4,z5,z8,z6]),(0,[z2,z3,z234,z4,z5,z8,z6]),(0,[z2,z3,z4,z235,z5,z8,z6]),(0,[z2,z3,z4,z5,z236,z8,z6])],[(0,[z237,z2,z3,z4,z5,z8,z6]),(0,[z2,z238,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z239,z6]),(0,[z240,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z241,z8,z6]),(0,[z2,z242,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z243]),(0,[z2,z3,z4,z5,z8,z244,z6]),(0,[z2,z3,z4,z245,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z246,z6]),(1,[z2,z107,z4,z5,z8,z39]),(0,[z2,z3,z4,z5,z8,z247,z6])],[(0,[z2,z3,z248,z4,z5,z8,z6]),(0,[z249,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z250,z8,z6]),(0,[z210,z2,z3,z4,z5,z8,z6]),(0,[z251,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z252,z6]),(0,[z2,z253,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z254,z6]),(0,[z2,z3,z4,z5,z255,z8,z6]),(0,[z2,z3,z4,z256,z5,z8,z6]),(0,[z2,z3,z4,z5,z257,z8,z6]),(0,[z50,z2,z3,z4,z5,z8,z38])],[(0,[z2,z3,z4,z5,z258,z8,z6]),(0,[z2,z3,z4,z18,z5,z8,z6])],[(0,[z52,z19,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z39]),(0,[z2,z3,z4,z5,z8,z259,z6]),(0,[z2,z260,z3,z4,z5,z8,z6]),(0,[z261,z2,z3,z4,z5,z8,z6]),(0,[z262,z2,z3,z4,z5,z8,z6])]],
   [[(0,[z3,z172,z4,z29,z5,z8,z6]),(0,[z2,z3,z4,z263,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z264]),(0,[z2,z3,z4,z5,z8,z265,z6]),(0,[z2,z3,z4,z5,z266,z8,z6]),(0,[z267,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z3,z4,z5,z8,z6]),(0,[z268,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z269,z6]),(0,[z2,z3,z270,z4,z5,z8,z6]),(0,[z2,z3,z114,z5,z8,z38,z6])],[(0,[z19,z154,z3,z4,z5,z8,z6]),(0,[z271,z2,z3,z4,z5,z8,z6]),(0,[z41,z2,z4,z5,z8,z44,z6]),(0,[z2,z272,z4,z225,z5,z8,z6]),(0,[z2,z3,z4,z199,z5,z174,z6])],[(0,[z273,z2,z3,z4,z5,z8,z6]),(0,[z274,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z275,z6]),(0,[z2,z276,z3,z4,z5,z8,z6]),(0,[z2,z3,z225,z5,z59,z8,z6])],[(0,[z2,z154,z3,z4,z5,z8,z277]),(0,[z2,z3,z4,z5,z5,z8,z6]),(0,[z2,z3,z4,z5,z278,z8,z6]),(0,[z2,z3,z4,z5,z8,z279,z6]),(0,[z280,z2,z3,z4,z5,z8,z6])],[(1,[z97,z3,z4,z5,z8,z83]),(0,[z98,z2,z4,z5,z8,z83,z6]),(0,[z2,z3,z281,z4,z5,z8,z6]),(1,[z50,z2,z3,z5,z8,z115]),(0,[z2,z3,z4,z5,z8,z282,z6])],[(0,[z52,z2,z283,z4,z5,z8,z6])],[(0,[z89,z2,z3,z4,z5,z100,z6]),(0,[z97,z3,z4,z5,z8,z83,z6]),(0,[z10,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z284,z8,z6]),(0,[z2,z3,z285,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z286,z6])]],
   [[(0,[z2,z3,z4,z5,z287,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z288]),(0,[z2,z3,z4,z5,z8,z289,z6]),(0,[z2,z3,z4,z290,z5,z8,z6]),(0,[z2,z3,z4,z291,z5,z8,z6]),(0,[z2,z292,z3,z4,z5,z8,z6])],[(0,[z293,z2,z3,z4,z5,z8,z6]),(0,[z2,z294,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z147,z8,z6]),(0,[z2,z15,z3,z4,z5,z101,z6]),(0,[z2,z3,z4,z5,z8,z295,z6])],[(0,[z2,z3,z4,z5,z8,z6,z296]),(0,[z2,z3,z4,z297,z5,z8,z6]),(0,[z89,z2,z3,z4,z5,z8,z159])],[(0,[z2,z3,z4,z74,z47,z8,z6]),(0,[z2,z3,z298,z4,z5,z8,z6]),(0,[z2,z3,z4,z299,z5,z8,z6]),(0,[z2,z3,z4,z300,z5,z8,z6])],[(0,[z301,z2,z3,z4,z5,z8,z6]),(0,[z3,z4,z5,z8,z83,z6,z116]),(0,[z2,z302,z3,z4,z129,z8,z6]),(0,[z2,z3,z4,z5,z303,z8,z6])],[(1,[z10,z2,z11,z5,z8,z6]),(0,[z2,z3,z4,z5,z304,z8,z6]),(0,[z41,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z305,z8,z6])],[(0,[z306,z2,z3,z4,z5,z8,z6]),(1,[z2,z302,z163,z5,z8,z6]),(0,[z307,z2,z3,z4,z5,z8,z6]),(0,[z2,z308,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z309]),(0,[z2,z310,z3,z4,z5,z8,z6]),(1,[z2,z173,z3,z4,z100,z6])],[(0,[z311,z2,z3,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z312,z4,z5,z8,z6]),(0,[z2,z3,z313,z4,z5,z8,z6]),(0,[z2,z314,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z315,z6]),(0,[z2,z3,z4,z5,z8,z6,z316]),(0,[z2,z3,z4,z317,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z318,z6])],[(0,[z2,z3,z4,z319,z5,z8,z6]),(0,[z2,z272,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z320])],[(0,[z82,z2,z3,z114,z4,z5,z8]),(0,[z2,z3,z4,z5,z321,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z322]),(0,[z323,z2,z3,z4,z5,z8,z6]),(0,[z2,z324,z3,z4,z5,z8,z6])],[(0,[z52,z2,z3,z4,z325,z8,z6]),(0,[z2,z3,z4,z326,z5,z8,z6]),(0,[z2,z3,z4,z5,z327,z8,z6]),(0,[z2,z3,z4,z328,z5,z8,z6]),(0,[z89,z2,z3,z4,z5,z174,z6]),(0,[z329,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z330,z8,z6]),(0,[z2,z3,z4,z5,z8,z331,z6]),(0,[z2,z3,z157,z5,z139,z8,z6]),(0,[z332,z2,z3,z4,z5,z8,z6]),(0,[z162,z2,z3,z4,z5,z87,z8]),(0,[z2,z3,z4,z333,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z6,z334]),(0,[z2,z3,z4,z335,z5,z8,z6]),(0,[z2,z3,z58,z4,z5,z8,z6]),(1,[z76,z2,z3,z59,z8,z6]),(1,[z1,z2,z3,z5,z137,z6])],[(0,[z2,z3,z4,z5,z8,z336,z6]),(0,[z2,z3,z4,z5,z8,z44,z115]),(0,[z2,z337,z3,z4,z5,z8,z6])],[(0,[z2,z3,z338,z4,z5,z8,z6]),(0,[z110,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z339,z8,z6]),(0,[z2,z3,z4,z5,z340,z8,z6]),(0,[z2,z3,z4,z5,z341,z8,z6])],[(0,[z2,z3,z4,z5,z342,z8,z6]),(0,[z2,z3,z343,z4,z5,z8,z6]),(0,[z50,z2,z3,z4,z117,z5,z8]),(0,[z2,z344,z3,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z4,z5,z8,z8,z6]),(0,[z2,z3,z4,z345,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z346]),(0,[z76,z2,z3,z4,z5,z8,z6]),(1,[z2,z4,z5,z347,z8,z6]),(0,[z2,z3,z4,z348,z5,z8,z6])],[(0,[z2,z3,z4,z5,z349,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z350]),(0,[z2,z3,z4,z5,z87,z8,z6])],[(0,[z2,z351,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z199,z225,z8,z6])],[(0,[z352,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z353]),(0,[z2,z3,z4,z354,z5,z8,z6]),(0,[z2,z3,z157,z4,z5,z6,z51]),(0,[z2,z3,z4,z132,z5,z8,z88]),(0,[z355,z2,z3,z4,z5,z8,z6])],[(0,[z356,z2,z3,z172,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z6]),(0,[z2,z357,z3,z4,z5,z8,z6]),(0,[z2,z13,z3,z4,z161,z8,z6]),(0,[z2,z4,z132,z5,z347,z8,z6])],[(0,[z184,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z358,z5,z8,z6]),(0,[z2,z359,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z161,z5,z8,z6]),(0,[z2,z3,z360,z4,z5,z8,z6]),(0,[z361,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z362,z4,z5,z8,z6])],[(0,[z2,z3,z4,z71,z29,z8,z6]),(0,[z2,z3,z363,z4,z5,z8,z6]),(0,[z2,z364,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z365,z8,z6]),(0,[z366,z2,z3,z4,z5,z8,z6])]],
   [[(0,[z154,z3,z283,z4,z5,z8,z6]),(1,[z356,z3,z29,z5,z8,z6]),(0,[z2,z367,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z368,z8,z6]),(0,[z2,z3,z4,z5,z369,z8,z6]),(0,[z50,z2,z3,z114,z5,z8,z6]),(0,[z2,z73,z4,z132,z5,z8,z6])],[(0,[z2,z370,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z371,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z44,z38]),(0,[z2,z3,z4,z372,z5,z8,z6]),(0,[z2,z3,z4,z373,z5,z8,z6]),(0,[z2,z3,z4,z5,z374,z8,z6])],[(0,[z2,z3,z4,z5,z8,z375,z6]),(0,[z376,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z117,z5,z8,z39]),(0,[z2,z377,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z277,z6]),(0,[z0,z2,z3,z4,z5,z8,z6]),(0,[z10,z2,z302,z4,z5,z8,z6]),(0,[z2,z3,z378,z4,z5,z8,z6]),(0,[z2,z379,z3,z4,z5,z8,z6])],[(0,[z52,z2,z3,z4,z60,z8,z6]),(0,[z2,z3,z4,z5,z380,z8,z6]),(0,[z2,z3,z157,z4,z5,z8,z6]),(0,[z381,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z382,z4,z5,z8,z6]),(1,[z162,z2,z3,z4,z87,z8])],[(0,[z2,z3,z4,z5,z8,z6,z383]),(0,[z2,z384,z3,z4,z5,z8,z6]),(0,[z2,z385,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z386]),(0,[z2,z3,z4,z387,z5,z8,z6])]],
   [[(0,[z355,z2,z3,z157,z4,z5,z6]),(0,[z2,z3,z4,z5,z388,z8,z6]),(0,[z2,z3,z4,z138,z5,z8,z6])],[(0,[z2,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z389,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z390]),(0,[z2,z3,z4,z5,z8,z391,z6]),(0,[z2,z3,z4,z392,z5,z8,z6]),(0,[z2,z3,z4,z199,z174,z8,z6]),(0,[z2,z3,z393,z4,z5,z8,z6]),(0,[z2,z3,z394,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z83,z51]),(0,[z2,z3,z4,z5,z395,z8,z6])],[(0,[z2,z3,z4,z5,z8,z396,z6]),(0,[z2,z3,z4,z5,z8,z44,z51]),(0,[z2,z3,z397,z4,z5,z8,z6])],[(0,[z2,z3,z398,z4,z29,z5,z6]),(0,[z184,z76,z2,z3,z4,z8,z6]),(0,[z399,z2,z3,z4,z5,z8,z6])],[(0,[z2,z4,z5,z147,z8,z101,z6]),(0,[z2,z3,z4,z400,z5,z8,z6])],[],[(0,[z2,z3,z4,z60,z5,z8,z6]),(0,[z2,z3,z4,z5,z401,z8,z6]),(0,[z2,z3,z4,z5,z8,z402,z6]),(0,[z162,z2,z3,z4,z132,z8,z6])]],
   [[(0,[z356,z2,z3,z29,z5,z8,z6]),(0,[z2,z403,z3,z4,z5,z8,z6]),(0,[z2,z13,z3,z4,z49,z8,z6]),(0,[z2,z404,z3,z4,z5,z8,z6])],[(0,[z19,z2,z283,z4,z5,z8,z6]),(1,[z2,z3,z4,z5,z8,z277]),(0,[z2,z3,z405,z4,z5,z8,z6])],[(0,[z19,z2,z4,z5,z8,z6,z39]),(0,[z82,z2,z3,z4,z5,z8,z116])],[(0,[z406,z2,z3,z4,z5,z8,z6]),(0,[z2,z407,z3,z4,z5,z8,z6]),(0,[z2,z163,z4,z11,z5,z8,z6]),(0,[z2,z3,z4,z199,z59,z8,z6]),(0,[z408,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z409,z5,z8,z6])],[(0,[z97,z2,z3,z4,z5,z8,z116]),(0,[z2,z3,z58,z225,z5,z8,z6]),(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z410,z8,z6])],[(0,[z2,z3,z4,z5,z8,z411,z6]),(0,[z412,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z413,z5,z8,z6]),(0,[z2,z3,z4,z5,z414,z8,z6]),(0,[z415,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z117,z5,z6,z51]),(0,[z2,z3,z4,z5,z416,z8,z6])],[(0,[z417,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z38,z170,z6]),(1,[z2,z3,z4,z199,z174,z6]),(1,[z2,z3,z4,z132,z8,z88])]],
   [[(0,[z2,z3,z4,z5,z418,z8,z6]),(0,[z2,z3,z4,z5,z8,z419,z6])],[(0,[z356,z2,z3,z4,z5,z8,z6]),(0,[z28,z2,z3,z4,z5,z8,z6]),(0,[z82,z2,z3,z4,z5,z8,z6]),(0,[z420,z2,z3,z4,z5,z8,z6])],[(0,[z2,z154,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z421,z6])],[(0,[z2,z3,z4,z422,z5,z8,z6]),(0,[z97,z2,z3,z4,z5,z8,z6]),(0,[z2,z4,z161,z5,z49,z8,z6]),(0,[z2,z3,z4,z5,z423,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z115]),(0,[z2,z3,z114,z4,z117,z5,z8])],[(0,[z2,z3,z4,z5,z8,z6,z424]),(0,[z2,z3,z4,z5,z8,z425,z6])],[(0,[z2,z3,z4,z426,z5,z8,z6]),(0,[z2,z427,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z6,z428]),(0,[z2,z3,z4,z5,z429,z8,z6]),(0,[z430,z2,z3,z4,z5,z8,z6]),(0,[z76,z2,z3,z5,z59,z8,z6])],[(0,[z2,z3,z431,z4,z5,z8,z6]),(0,[z432,z2,z3,z4,z5,z8,z6]),(0,[z2,z433,z3,z4,z5,z8,z6])]],
   [[(0,[z434,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z117,z5,z8,z6])],[(0,[z2,z3,z283,z4,z5,z8,z6]),(1,[z184,z3,z4,z112,z8,z6]),(0,[z97,z82,z3,z4,z5,z8,z6]),(0,[z2,z435,z3,z4,z5,z8,z6]),(0,[z436,z2,z3,z4,z5,z8,z6])],[(0,[z2,z437,z3,z4,z5,z8,z6]),(0,[z2,z3,z398,z4,z5,z8,z6]),(0,[z2,z15,z3,z4,z5,z147,z6]),(0,[z438,z2,z3,z4,z5,z8,z6]),(0,[z2,z439,z3,z4,z5,z8,z6])],[(1,[z2,z3,z398,z4,z5,z6]),(1,[z0,z3,z4,z5,z47,z6]),(0,[z2,z3,z4,z5,z440,z8,z6]),(0,[z441,z2,z3,z4,z5,z8,z6])],[(0,[z2,z13,z163,z4,z5,z8,z6]),(0,[z1,z2,z3,z4,z5,z139,z6])],[(0,[z442,z2,z3,z4,z5,z8,z6]),(0,[z146,z2,z3,z4,z5,z101,z6]),(0,[z443,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z444]),(0,[z2,z3,z445,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z446,z8,z6])],[(0,[z2,z3,z4,z447,z5,z8,z6]),(0,[z2,z3,z4,z448,z5,z8,z6]),(0,[z449,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z450]),(0,[z2,z3,z4,z5,z8,z6,z451])],[(0,[z2,z3,z452,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z4,z5,z453,z8,z6]),(0,[z2,z454,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z199,z161,z8,z6]),(0,[z2,z4,z5,z8,z44,z6,z39]),(0,[z455,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z456,z6])],[(0,[z2,z3,z457,z4,z5,z8,z6]),(0,[z458,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z459,z8,z6]),(0,[z460,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z461,z5,z8,z6])],[(0,[z2,z3,z4,z5,z462,z8,z6]),(0,[z2,z3,z463,z4,z5,z8,z6])],[(0,[z464,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z465,z6]),(0,[z2,z3,z4,z174,z8,z100,z6])],[(0,[z2,z3,z4,z466,z5,z8,z6]),(0,[z2,z3,z467,z4,z5,z8,z6])],[(0,[z2,z468,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z469,z8,z6]),(0,[z2,z470,z3,z4,z5,z8,z6]),(0,[z2,z471,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z472,z8,z6]),(0,[z2,z473,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z474,z5,z8,z6]),(0,[z355,z2,z3,z4,z5,z109,z6])],[(0,[z2,z475,z3,z4,z5,z8,z6]),(1,[z146,z2,z4,z5,z147,z6]),(0,[z2,z3,z4,z476,z5,z8,z6]),(0,[z2,z3,z4,z5,z477,z8,z6])]],
   [[(0,[z478,z2,z3,z4,z5,z8,z6]),(0,[z355,z2,z3,z4,z5,z8,z51])],[(0,[z479,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z51])],[(0,[z480,z2,z3,z4,z5,z8,z6])],[(0,[z2,z481,z3,z4,z5,z8,z6]),(0,[z482,z2,z3,z4,z5,z8,z6]),(0,[z2,z483,z3,z4,z5,z8,z6]),(1,[z2,z3,z4,z5,z8,z288]),(0,[z2,z3,z4,z5,z8,z484,z6]),(0,[z2,z15,z3,z4,z5,z8,z6]),(0,[z485,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z6,z486]),(0,[z487,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z488,z4,z5,z8,z6]),(0,[z2,z302,z3,z4,z20,z8,z6]),(0,[z2,z3,z4,z5,z489,z8,z6]),(0,[z2,z3,z4,z5,z8,z490,z6]),(0,[z2,z3,z4,z5,z8,z491,z6]),(1,[z2,z3,z4,z5,z456,z6])],[(0,[z2,z3,z492,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z493,z8,z6]),(0,[z89,z2,z3,z4,z5,z47,z6]),(0,[z0,z2,z3,z4,z5,z100,z6]),(0,[z494,z2,z3,z4,z5,z8,z6])],[(0,[z495,z2,z3,z4,z5,z8,z6]),(0,[z2,z13,z3,z4,z5,z8,z6]),(0,[z2,z496,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z117,z5,z109,z8])],[(0,[z111,z2,z3,z4,z5,z8,z6]),(0,[z97,z2,z3,z114,z4,z5,z8]),(0,[z2,z497,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z498,z8,z6]),(0,[z2,z3,z4,z5,z8,z499,z6])]],
   [[(0,[z2,z3,z4,z500,z5,z8,z6])],[(1,[z2,z272,z4,z5,z8,z6]),(0,[z2,z3,z4,z132,z5,z8,z6])],[(0,[z50,z82,z2,z3,z4,z5,z8])],[(0,[z2,z3,z4,z5,z501,z8,z6])],[(0,[z2,z3,z4,z502,z5,z8,z6]),(0,[z2,z3,z4,z199,z49,z8,z6]),(0,[z2,z3,z4,z5,z8,z503,z6])],[(0,[z2,z3,z4,z5,z504,z8,z6]),(0,[z2,z3,z4,z129,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z505,z6]),(0,[z162,z2,z3,z4,z5,z8,z88])],[(0,[z506,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z507,z5,z8,z6])],[(0,[z508,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z509,z4,z5,z8,z6]),(0,[z82,z2,z3,z4,z5,z8,z39]),(0,[z2,z3,z4,z5,z8,z510,z6])]],
   [[(0,[z2,z3,z511,z4,z5,z8,z6]),(0,[z2,z4,z5,z49,z8,z6,z39]),(0,[z512,z2,z3,z4,z5,z8,z6])],[(0,[z220,z2,z3,z172,z5,z8,z6]),(0,[z0,z2,z3,z4,z5,z174,z6]),(0,[z97,z2,z3,z4,z5,z8,z39]),(0,[z2,z4,z5,z8,z83,z190,z6]),(0,[z2,z173,z3,z4,z5,z8,z6])],[(0,[z513,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z514,z6]),(0,[z2,z3,z4,z515,z5,z8,z6]),(0,[z2,z3,z4,z516,z5,z8,z6]),(1,[z2,z14,z4,z49,z8,z6])],[(1,[z2,z42,z3,z4,z5,z6]),(0,[z2,z483,z3,z4,z29,z5,z8]),(0,[z2,z3,z517,z4,z5,z8,z6]),(0,[z111,z2,z3,z4,z135,z8,z6]),(0,[z2,z3,z4,z5,z518,z8,z6]),(0,[z2,z15,z4,z5,z8,z101,z6]),(0,[z519,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z520,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z521]),(0,[z2,z3,z4,z5,z522,z8,z6]),(0,[z2,z3,z4,z5,z8,z523,z6]),(0,[z2,z3,z4,z5,z8,z524,z6])],[(0,[z525,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z526]),(0,[z2,z3,z4,z5,z527,z8,z6])],[(0,[z2,z3,z4,z5,z8,z528,z6]),(0,[z2,z3,z4,z5,z529,z8,z6]),(0,[z1,z2,z3,z4,z414,z8,z6])],[(1,[z2,z3,z4,z5,z8,z6]),(0,[z530,z2,z3,z4,z5,z8,z6]),(1,[z2,z3,z58,z225,z8,z6]),(0,[z2,z3,z4,z5,z8,z531,z6])]],
   [[(0,[z2,z3,z4,z5,z532,z8,z6]),(0,[z2,z3,z4,z5,z8,z533,z6]),(0,[z534,z2,z3,z4,z5,z8,z6]),(0,[z41,z2,z3,z4,z5,z8,z44])],[(0,[z2,z3,z4,z5,z535,z8,z6]),(0,[z2,z302,z3,z163,z5,z8,z6]),(0,[z2,z14,z3,z4,z161,z8,z6]),(0,[z2,z3,z4,z5,z536,z8,z6])],[(1,[z89,z3,z4,z5,z48,z6])],[(0,[z537,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z538,z8,z6])],[(0,[z110,z2,z3,z4,z29,z8,z6]),(0,[z2,z3,z4,z5,z539,z8,z6])],[(0,[z2,z3,z4,z5,z8,z540,z6]),(0,[z2,z3,z4,z74,z5,z8,z6]),(0,[z2,z3,z541,z4,z5,z8,z6]),(0,[z1,z2,z3,z4,z5,z6,z51])],[(0,[z542,z2,z3,z4,z5,z8,z6]),(1,[z98,z2,z4,z5,z8,z6]),(0,[z543,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z544,z8,z6])],[(0,[z52,z2,z154,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z545,z8,z6]),(0,[z2,z3,z4,z135,z5,z155,z6]),(0,[z2,z3,z4,z5,z8,z546,z6]),(0,[z2,z3,z4,z5,z8,z6,z547]),(0,[z2,z3,z548,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z4,z5,z8,z549,z6])],[(0,[z52,z2,z163,z4,z5,z8,z6]),(0,[z550,z2,z3,z4,z5,z8,z6]),(0,[z551,z2,z3,z4,z5,z8,z6]),(0,[z552,z2,z3,z4,z5,z8,z6])],[(0,[z2,z154,z3,z4,z5,z8,z486]),(0,[z184,z3,z4,z5,z112,z8,z6]),(0,[z0,z2,z3,z4,z5,z48,z6]),(0,[z2,z107,z3,z4,z5,z8,z39]),(0,[z2,z3,z4,z5,z8,z6,z553]),(0,[z2,z3,z4,z554,z5,z8,z6]),(1,[z2,z3,z4,z5,z8,z386]),(0,[z555,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z556,z4,z5,z8,z6])],[(0,[z557,z2,z3,z4,z5,z8,z6]),(0,[z2,z558,z3,z4,z5,z8,z6])],[(0,[z220,z2,z3,z29,z5,z8,z6]),(0,[z2,z559,z3,z4,z5,z8,z6]),(0,[z560,z2,z3,z4,z5,z8,z6]),(0,[z561,z2,z3,z4,z5,z8,z6])],[(0,[z52,z10,z2,z4,z5,z8,z6]),(0,[z2,z3,z4,z562,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z563,z6]),(1,[z2,z3,z4,z5,z8,z490])],[(0,[z2,z3,z4,z5,z564,z8,z6]),(0,[z2,z3,z565,z4,z5,z8,z6]),(0,[z566,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z567]),(0,[z2,z3,z4,z5,z63,z8,z6]),(0,[z2,z3,z4,z568,z5,z8,z6])]],
   [[(0,[z569,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z570,z8,z6])],[(0,[z571,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z572,z5,z8,z6]),(0,[z2,z3,z4,z5,z573,z8,z6]),(0,[z2,z574,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z135,z5,z23,z6]),(0,[z575,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z576,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z577,z6]),(0,[z2,z3,z4,z5,z8,z578,z6]),(0,[z2,z3,z4,z5,z8,z579,z6]),(0,[z2,z3,z4,z5,z580,z8,z6])],[(0,[z41,z2,z107,z4,z5,z8,z6])],[(0,[z2,z3,z581,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z582,z8,z6])],[(0,[z583,z2,z3,z4,z5,z8,z6]),(0,[z2,z14,z3,z4,z49,z8,z6]),(0,[z2,z3,z4,z5,z139,z8,z6]),(0,[z1,z2,z3,z5,z8,z137,z6]),(0,[z50,z2,z3,z5,z8,z6,z115])],[(0,[z220,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z584,z6]),(0,[z2,z3,z4,z5,z112,z8,z6]),(0,[z146,z2,z3,z4,z5,z147,z6]),(0,[z355,z2,z3,z4,z117,z5,z6])],[(0,[z2,z3,z4,z585,z5,z8,z6]),(0,[z2,z3,z4,z586,z5,z8,z6]),(0,[z89,z2,z3,z4,z5,z8,z288]),(0,[z2,z3,z4,z587,z5,z8,z6]),(0,[z2,z3,z4,z588,z5,z8,z6]),(0,[z2,z589,z3,z4,z5,z8,z6]),(1,[z2,z3,z4,z138,z5,z8]),(0,[z210,z2,z3,z4,z5,z38,z6])]],
   [[(1,[z52,z283,z4,z5,z8,z6]),(0,[z2,z3,z4,z590,z5,z8,z6]),(0,[z591,z2,z3,z4,z5,z8,z6]),(0,[z76,z2,z3,z58,z5,z8,z6]),(0,[z592,z2,z3,z4,z5,z8,z6]),(1,[z355,z2,z3,z4,z117,z5])],[(0,[z593,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z190,z6]),(0,[z2,z4,z225,z5,z369,z8,z6]),(0,[z594,z2,z3,z4,z5,z8,z6])],[(0,[z595,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z596,z5,z8,z6]),(0,[z2,z3,z4,z199,z5,z8,z6])],[(0,[z2,z597,z3,z4,z5,z8,z6]),(0,[z598,z2,z3,z4,z5,z8,z6]),(0,[z599,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z16]),(0,[z2,z3,z4,z5,z600,z8,z6])],[(0,[z2,z3,z4,z135,z49,z8,z6]),(0,[z2,z601,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z602,z6]),(0,[z603,z2,z3,z4,z5,z8,z6])],[(0,[z10,z2,z3,z4,z5,z8,z182]),(0,[z2,z3,z4,z11,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z604,z6]),(0,[z2,z3,z605,z4,z5,z8,z6]),(0,[z2,z3,z4,z606,z5,z8,z6])],[(0,[z607,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z608,z6]),(0,[z2,z3,z4,z29,z5,z8,z6]),(0,[z2,z609,z3,z4,z5,z8,z6]),(1,[z2,z4,z5,z369,z8,z6])],[(0,[z97,z50,z2,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z8,z610,z6])]],
   [[(0,[z2,z611,z3,z4,z5,z8,z6]),(0,[z10,z2,z13,z4,z5,z8,z6]),(1,[z2,z3,z4,z7,z8,z6]),(0,[z2,z3,z4,z5,z139,z8,z386]),(0,[z2,z3,z4,z5,z612,z8,z6])],[(0,[z356,z220,z3,z4,z5,z8,z6]),(0,[z613,z2,z3,z4,z5,z8,z6]),(0,[z146,z2,z15,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z614,z6]),(0,[z2,z3,z4,z5,z615,z8,z6]),(0,[z2,z3,z4,z132,z5,z456,z6])],[(0,[z2,z3,z4,z5,z616,z8,z6]),(0,[z2,z302,z163,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z617,z8,z6])],[(0,[z10,z2,z4,z11,z5,z8,z6]),(1,[z2,z3,z4,z5,z8,z16]),(0,[z2,z3,z4,z5,z8,z618,z6]),(0,[z2,z3,z5,z139,z8,z137,z6]),(0,[z2,z3,z4,z5,z8,z6,z619])],[(1,[z19,z154,z4,z5,z8,z6]),(0,[z184,z111,z3,z4,z5,z8,z6]),(0,[z2,z620,z3,z4,z5,z8,z6]),(0,[z2,z163,z4,z5,z49,z8,z6]),(0,[z2,z3,z4,z5,z8,z621,z6]),(0,[z2,z3,z4,z5,z8,z100,z6]),(0,[z2,z3,z4,z5,z622,z8,z6]),(1,[z2,z3,z4,z5,z109,z51])],[(0,[z2,z3,z4,z5,z8,z623,z6]),(0,[z2,z3,z4,z5,z8,z624,z6]),(0,[z625,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z626,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z182,z6]),(0,[z41,z2,z13,z4,z5,z8,z6]),(0,[z2,z3,z4,z132,z5,z87,z8])],[(0,[z2,z3,z4,z4,z5,z8,z6]),(0,[z10,z2,z3,z4,z5,z8,z191]),(0,[z146,z2,z3,z4,z5,z8,z6]),(0,[z2,z107,z3,z4,z5,z8,z6]),(0,[z2,z627,z3,z4,z5,z8,z6]),(0,[z355,z2,z3,z4,z5,z100,z6]),(0,[z2,z628,z3,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z629,z4,z5,z8,z6]),(0,[z2,z3,z630,z4,z5,z8,z6])],[(0,[z10,z2,z3,z163,z5,z8,z6]),(0,[z2,z3,z4,z5,z631,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z632])],[(0,[z2,z302,z3,z11,z5,z8,z6]),(0,[z2,z173,z3,z4,z5,z100,z6]),(0,[z2,z633,z3,z4,z5,z8,z6]),(1,[z2,z73,z4,z5,z8,z6])],[(0,[z76,z111,z2,z3,z4,z8,z6]),(0,[z2,z3,z4,z5,z634,z8,z6]),(0,[z89,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z635,z8,z6]),(0,[z2,z636,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z637,z5,z8,z6])],[(0,[z2,z3,z4,z5,z325,z8,z6]),(0,[z82,z2,z3,z4,z5,z8,z44]),(0,[z2,z3,z4,z5,z8,z638,z6])],[(0,[z2,z3,z4,z639,z5,z8,z6]),(0,[z2,z42,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z640,z5,z8,z6])],[(0,[z356,z3,z4,z29,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z641]),(0,[z2,z3,z4,z5,z642,z8,z6])],[(0,[z184,z2,z3,z4,z112,z8,z6]),(0,[z2,z3,z4,z161,z112,z8,z6]),(0,[z2,z13,z4,z5,z8,z6,z39]),(0,[z2,z3,z58,z4,z161,z8,z6]),(0,[z2,z3,z4,z5,z643,z8,z6])]],
   [[(0,[z2,z3,z4,z644,z5,z8,z6]),(0,[z184,z2,z3,z58,z4,z8,z6]),(0,[z2,z3,z4,z112,z49,z8,z6]),(0,[z2,z3,z4,z5,z133,z8,z6])],[(0,[z2,z3,z645,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z39,z115]),(1,[z2,z3,z4,z414,z8,z6])],[(1,[z220,z3,z172,z5,z8,z6]),(1,[z2,z3,z157,z5,z139,z6])],[(0,[z52,z3,z283,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z646,z6]),(0,[z647,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z117,z5,z8,z44]),(0,[z2,z3,z4,z5,z8,z648,z6]),(0,[z2,z3,z4,z5,z8,z38,z6]),(0,[z355,z2,z3,z4,z5,z174,z6]),(0,[z2,z3,z4,z5,z8,z6,z88]),(0,[z2,z3,z4,z5,z109,z8,z6])],[(0,[z2,z302,z3,z4,z5,z8,z6]),(0,[z649,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z5,z8,z38,z6,z115])],[(0,[z650,z2,z3,z4,z5,z8,z6]),(0,[z0,z3,z4,z5,z47,z8,z6]),(0,[z2,z3,z651,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z652,z8,z6])],[(0,[z2,z3,z4,z5,z8,z30,z6]),(0,[z2,z3,z4,z653,z5,z8,z6]),(0,[z2,z654,z3,z4,z5,z8,z6])],[(0,[z2,z655,z3,z4,z5,z8,z6]),(1,[z2,z3,z4,z5,z8,z486]),(1,[z111,z3,z4,z135,z8,z6]),(0,[z2,z3,z4,z5,z8,z656,z6]),(0,[z2,z3,z4,z5,z8,z657,z6])]],
   [[(0,[z2,z3,z4,z658,z5,z8,z6]),(0,[z89,z2,z3,z157,z4,z5,z6]),(0,[z2,z3,z659,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z660,z6])],[(0,[z1,z355,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z661,z8,z6]),(0,[z2,z3,z662,z4,z5,z8,z6]),(0,[z2,z3,z157,z4,z5,z137,z6]),(1,[z2,z3,z4,z5,z133,z6])],[(0,[z2,z3,z663,z4,z5,z8,z6]),(1,[z28,z2,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z664,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z665]),(0,[z355,z2,z3,z4,z117,z5,z8])],[(0,[z184,z2,z3,z4,z8,z100,z6]),(0,[z2,z3,z4,z5,z666,z8,z6]),(0,[z2,z3,z4,z161,z8,z100,z6]),(0,[z2,z15,z3,z4,z5,z8,z490]),(0,[z2,z667,z3,z4,z5,z8,z6])],[(0,[z668,z2,z3,z4,z5,z8,z6]),(0,[z669,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z670,z8,z6])]],
   [[],[(0,[z2,z3,z671,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z159,z6]),(0,[z2,z3,z4,z5,z8,z48,z6]),(0,[z672,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z673,z6]),(0,[z674,z2,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z135,z5,z8,z6]),(0,[z2,z3,z675,z4,z5,z8,z6]),(0,[z2,z676,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z677,z8,z6]),(0,[z2,z3,z58,z4,z49,z8,z6]),(0,[z2,z3,z4,z678,z5,z8,z6]),(0,[z2,z3,z4,z5,z174,z8,z6]),(0,[z2,z3,z4,z5,z8,z679,z6])],[(0,[z680,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z163,z4,z5,z8,z6]),(0,[z2,z3,z4,z681,z5,z8,z6]),(0,[z682,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z58,z4,z225,z8,z6])],[(0,[z2,z3,z4,z5,z8,z683,z6]),(0,[z2,z3,z4,z5,z8,z684,z6])],[(0,[z2,z4,z297,z29,z5,z8,z6]),(1,[z2,z3,z141,z4,z5,z8]),(1,[z2,z13,z4,z161,z8,z6])],[(1,[z2,z483,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z8,z685,z6]),(0,[z76,z2,z3,z4,z49,z8,z6]),(0,[z2,z3,z4,z5,z8,z39,z51]),(0,[z2,z3,z4,z225,z5,z8,z6]),(0,[z2,z3,z4,z5,z686,z8,z6]),(0,[z687,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z688,z4,z5,z8,z6])]],
   [[(0,[z184,z2,z3,z4,z199,z8,z6]),(0,[z689,z2,z3,z4,z5,z8,z6]),(0,[z76,z2,z3,z4,z225,z8,z6]),(0,[z2,z3,z690,z4,z5,z8,z6]),(0,[z162,z2,z3,z4,z87,z8,z6])],[(0,[z2,z3,z691,z4,z5,z8,z6]),(0,[z692,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z693,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z694,z8,z6])],[(0,[z2,z3,z4,z5,z8,z6,z695]),(0,[z696,z2,z3,z4,z5,z8,z6]),(0,[z697,z2,z3,z4,z5,z8,z6]),(0,[z2,z3,z114,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z347,z8,z6])],[(1,[z2,z4,z297,z5,z8,z6]),(0,[z2,z3,z4,z5,z698,z8,z6]),(0,[z2,z699,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z6,z700])],[(1,[z2,z3,z4,z325,z8,z6])],[(0,[z2,z3,z4,z701,z5,z8,z6]),(0,[z2,z13,z4,z161,z5,z8,z6]),(0,[z2,z3,z4,z5,z59,z8,z6]),(0,[z2,z3,z4,z702,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z116,z51]),(0,[z2,z3,z4,z5,z8,z703,z6]),(0,[z2,z3,z4,z704,z5,z8,z6])],[(0,[z2,z3,z4,z705,z5,z8,z6]),(0,[z2,z3,z4,z706,z5,z8,z6]),(0,[z2,z15,z3,z4,z7,z8,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z2,z3,z4,z707,z8,z6]),(0,[z2,z3,z4,z8,z708,z6]),(1,[z3,z4,z5,z709,z6]),(0,[z0,z3,z4,z5,z709,z6]),(0,[z2,z3,z4,z5,z44,z170]),(0,[z2,z3,z4,z5,z331,z51])],[(0,[z2,z3,z4,z502,z174,z6]),(0,[z2,z163,z710,z5,z8,z6]),(0,[z2,z3,z4,z5,z711,z6]),(0,[z2,z3,z4,z5,z401,z51])],[(0,[z19,z154,z4,z5,z8,z277]),(0,[z2,z107,z4,z5,z8,z712]),(0,[z2,z3,z4,z5,z713,z6]),(0,[z2,z3,z4,z626,z100,z6])],[(0,[z2,z3,z4,z5,z8,z714]),(0,[z2,z3,z4,z5,z236,z51]),(0,[z412,z3,z4,z5,z8,z83]),(0,[z2,z3,z4,z129,z8,z6]),(0,[z2,z163,z5,z489,z8,z6]),(0,[z2,z3,z4,z715,z8,z6]),(0,[z76,z2,z3,z59,z8,z6]),(0,[z1,z2,z3,z5,z137,z6]),(0,[z2,z716,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z4,z5,z717,z6]),(0,[z2,z4,z5,z718,z8,z6]),(0,[z10,z2,z11,z5,z8,z191])],[(0,[z2,z3,z719,z5,z8,z6]),(0,[z356,z28,z29,z5,z8,z6]),(0,[z720,z2,z3,z4,z5,z8])],[(0,[z28,z2,z42,z4,z5,z6]),(0,[z2,z3,z4,z5,z721,z6]),(0,[z10,z2,z710,z5,z8,z6]),(0,[z722,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z63,z8,z6]),(0,[z2,z3,z4,z7,z8,z490]),(0,[z2,z3,z157,z5,z723,z6])],[(0,[z3,z4,z5,z8,z724,z6]),(0,[z2,z4,z5,z347,z8,z6]),(0,[z2,z3,z4,z5,z8,z725])]],
   [[(0,[z2,z42,z4,z297,z5,z6]),(0,[z726,z3,z4,z5,z8,z6]),(0,[z727,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z728]),(0,[z210,z2,z3,z114,z5,z38])],[(0,[z2,z3,z4,z729,z8,z6]),(0,[z2,z3,z730,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z731]),(0,[z2,z3,z732,z4,z5,z6]),(0,[z2,z4,z5,z8,z44,z712]),(0,[z2,z260,z3,z4,z100,z6]),(0,[z2,z3,z157,z5,z139,z6]),(1,[z2,z3,z4,z733,z5])],[(0,[z2,z3,z4,z71,z8,z6]),(0,[z2,z42,z3,z141,z4,z5]),(0,[z2,z4,z5,z8,z734,z6]),(0,[z2,z735,z4,z5,z8,z6]),(0,[z3,z4,z5,z709,z8,z6]),(0,[z2,z363,z4,z49,z8,z6]),(0,[z2,z3,z4,z736,z8,z6]),(0,[z2,z3,z4,z5,z737,z8])],[(0,[z2,z3,z4,z5,z8,z738]),(0,[z2,z739,z4,z5,z8,z6]),(0,[z2,z4,z5,z8,z190,z51]),(0,[z740,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z741])]],
   [[(0,[z10,z2,z639,z5,z8,z6]),(0,[z2,z3,z157,z4,z5,z288]),(0,[z2,z4,z5,z8,z712,z39])],[(0,[z2,z3,z4,z742,z8,z6]),(0,[z2,z3,z4,z5,z743,z6]),(0,[z3,z4,z5,z8,z744,z6])],[(0,[z19,z4,z263,z5,z8,z6]),(0,[z19,z4,z5,z8,z265,z6]),(0,[z2,z3,z4,z5,z8,z745]),(0,[z746,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z747]),(0,[z2,z4,z748,z49,z8,z6]),(0,[z2,z4,z5,z749,z8,z6]),(0,[z2,z3,z5,z139,z723,z6]),(0,[z2,z3,z114,z5,z8,z38])],[(0,[z356,z110,z3,z29,z8,z6]),(0,[z2,z750,z4,z5,z8,z6]),(0,[z2,z324,z4,z49,z8,z6]),(0,[z355,z2,z3,z4,z5,z194])]],
   [[(0,[z111,z3,z4,z135,z155,z6])],[(0,[z2,z163,z4,z325,z8,z6]),(0,[z2,z751,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z752,z6]),(0,[z2,z3,z4,z5,z753,z6])],[(0,[z754,z2,z3,z4,z8,z6]),(0,[z2,z4,z5,z755,z8,z6]),(0,[z756,z3,z4,z5,z8,z6]),(0,[z10,z2,z160,z5,z8,z6]),(0,[z2,z3,z4,z757,z8,z6])],[(0,[z2,z3,z4,z5,z8,z6]),(0,[z19,z2,z4,z5,z8,z191]),(0,[z2,z3,z4,z5,z8,z758]),(0,[z2,z3,z710,z5,z8,z6]),(0,[z2,z4,z5,z759,z101,z6]),(0,[z2,z3,z4,z132,z456,z88])]],
   [[(0,[z0,z3,z4,z74,z47,z6]),(0,[z2,z3,z4,z5,z8,z760]),(0,[z2,z3,z4,z5,z8,z712]),(0,[z41,z2,z4,z5,z8,z712]),(0,[z2,z3,z157,z5,z139,z386])],[(0,[z761,z2,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z762,z6]),(0,[z2,z3,z4,z5,z8,z763]),(0,[z162,z2,z3,z4,z87,z8])],[(0,[z10,z2,z4,z325,z8,z6]),(0,[z2,z3,z764,z4,z5,z8]),(0,[z28,z2,z141,z4,z5,z8]),(0,[z2,z765,z3,z4,z5,z8]),(0,[z766,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z767,z8,z6]),(0,[z2,z3,z4,z5,z8,z768]),(0,[z2,z483,z4,z297,z5,z8]),(0,[z2,z4,z5,z8,z769,z6]),(0,[z89,z2,z3,z4,z414,z6]),(0,[z2,z14,z4,z748,z8,z6]),(0,[z2,z770,z4,z5,z8,z6])]],
   [[(0,[z2,z3,z4,z771,z8,z6]),(0,[z52,z772,z4,z5,z8,z6]),(0,[z2,z3,z773,z4,z5,z8]),(0,[z774,z3,z4,z5,z8,z6]),(0,[z2,z3,z114,z4,z5,z170])],[(0,[z76,z2,z3,z701,z8,z6]),(0,[z2,z775,z4,z5,z8,z6]),(0,[z82,z3,z4,z5,z8,z614]),(0,[z2,z3,z4,z5,z8,z776]),(0,[z2,z3,z4,z5,z8,z777]),(0,[z2,z3,z4,z778,z8,z6]),(0,[z2,z3,z114,z5,z8,z684]),(0,[z2,z3,z4,z733,z5,z8])],[(0,[z2,z3,z4,z5,z779,z6]),(0,[z98,z2,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z780]),(0,[z356,z42,z3,z29,z5,z6]),(0,[z2,z3,z114,z256,z5,z8]),(0,[z2,z3,z4,z5,z781,z8])],[(0,[z2,z3,z782,z4,z5,z6]),(0,[z2,z3,z4,z783,z8,z6]),(0,[z89,z3,z4,z5,z709,z6]),(0,[z82,z470,z3,z4,z5,z8]),(0,[z2,z3,z784,z4,z5,z8]),(0,[z2,z3,z4,z7,z8,z16]),(0,[z76,z2,z3,z785,z8,z6]),(0,[z2,z3,z4,z5,z8,z786])]],
   [[(1,[z772,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z787]),(0,[z2,z3,z4,z5,z788,z6])],[(0,[z2,z3,z4,z789,z8,z6]),(0,[z2,z3,z141,z4,z5,z8]),(0,[z2,z3,z4,z5,z790,z6]),(0,[z2,z3,z58,z358,z8,z6]),(0,[z111,z3,z4,z8,z656,z6]),(0,[z2,z3,z791,z4,z5,z6])],[(0,[z2,z3,z4,z792,z8,z6]),(0,[z2,z483,z3,z4,z5,z8]),(0,[z2,z793,z4,z5,z8,z6]),(0,[z2,z435,z4,z5,z8,z39]),(0,[z2,z3,z4,z5,z8,z386]),(0,[z1,z2,z3,z348,z5,z6])],[(0,[z2,z3,z4,z5,z8,z794]),(0,[z2,z3,z4,z8,z795,z6]),(0,[z2,z3,z796,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z797]),(0,[z2,z3,z4,z87,z737,z8])]],
   [[(0,[z52,z2,z4,z5,z8,z486]),(0,[z110,z2,z3,z141,z4,z8]),(0,[z2,z3,z4,z5,z23,z6]),(0,[z2,z3,z157,z507,z5,z6]),(0,[z2,z3,z4,z798,z8,z6]),(0,[z2,z3,z4,z5,z8,z799]),(0,[z2,z4,z5,z759,z8,z6]),(0,[z800,z2,z3,z5,z8,z6]),(0,[z2,z3,z4,z5,z723,z6]),(0,[z801,z2,z4,z5,z8,z6])],[(0,[z802,z2,z4,z5,z8,z6]),(0,[z92,z2,z3,z59,z8,z6]),(0,[z2,z803,z4,z5,z8,z6]),(0,[z2,z804,z4,z5,z8,z6])],[(0,[z52,z314,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z805,z8])],[(0,[z2,z3,z4,z325,z8,z6]),(0,[z41,z2,z4,z325,z8,z6]),(0,[z806,z2,z3,z4,z8,z6]),(0,[z2,z807,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z709,z6]),(0,[z2,z3,z4,z808,z8,z6])]],
   [[(0,[z41,z2,z4,z5,z8,z208]),(0,[z28,z2,z483,z4,z5,z8]),(0,[z443,z2,z3,z5,z8,z115])],[(0,[z2,z3,z4,z5,z8,z809]),(0,[z2,z3,z4,z5,z8,z810]),(0,[z2,z3,z4,z811,z8,z6]),(0,[z594,z2,z3,z4,z100,z6])],[(0,[z2,z3,z4,z5,z812,z6]),(0,[z2,z238,z4,z49,z8,z6]),(0,[z2,z3,z4,z813,z8,z6]),(0,[z2,z3,z4,z333,z174,z6]),(0,[z2,z3,z4,z132,z8,z88])],[(0,[z356,z3,z71,z29,z8,z6]),(0,[z184,z385,z3,z4,z8,z6]),(0,[z2,z4,z5,z8,z814,z6]),(0,[z3,z4,z5,z8,z83,z724]),(0,[z2,z107,z4,z5,z8,z39])]],
   [[(0,[z2,z3,z4,z5,z8,z815]),(0,[z2,z3,z4,z733,z5,z51])],[(0,[z2,z3,z5,z8,z723,z6])],[(0,[z816,z2,z3,z5,z8,z6]),(0,[z2,z3,z4,z5,z817,z8]),(0,[z2,z3,z141,z398,z4,z5]),(0,[z2,z3,z4,z5,z818,z6]),(0,[z97,z3,z4,z5,z8,z724]),(1,[z2,z4,z5,z8,z712]),(0,[z2,z3,z4,z18,z8,z6]),(0,[z2,z3,z4,z199,z498,z6])],[(0,[z2,z3,z4,z819,z8,z6]),(0,[z28,z2,z398,z4,z5,z6]),(0,[z2,z483,z3,z398,z4,z5]),(0,[z2,z3,z820,z5,z8,z6]),(0,[z2,z3,z4,z5,z821,z6]),(0,[z2,z344,z4,z5,z8,z39]),(0,[z2,z3,z157,z4,z5,z386]),(0,[z2,z3,z4,z117,z5,z615]),(0,[z2,z4,z5,z822,z8,z6])]],
   [[(0,[z52,z283,z4,z5,z8,z6]),(0,[z2,z3,z4,z8,z823,z6]),(0,[z2,z824,z4,z5,z8,z6]),(0,[z355,z2,z3,z4,z117,z5])],[(0,[z2,z3,z4,z825,z8,z6]),(0,[z2,z3,z4,z8,z30,z6]),(0,[z2,z4,z826,z5,z8,z6]),(0,[z1,z2,z3,z706,z5,z6]),(0,[z827,z3,z4,z5,z8,z6]),(0,[z2,z828,z4,z5,z8,z6]),(0,[z2,z3,z114,z5,z8,z829])],[(0,[z2,z141,z4,z297,z5,z8]),(0,[z2,z3,z4,z5,z830,z6]),(0,[z2,z3,z4,z5,z8,z831]),(0,[z534,z2,z4,z5,z8,z39]),(0,[z832,z3,z4,z5,z8,z6])],[(0,[z2,z4,z5,z833,z8,z6]),(0,[z2,z3,z4,z834,z8,z6]),(0,[z2,z3,z4,z835,z8,z6])]],
   [[(0,[z2,z3,z141,z4,z71,z8]),(0,[z184,z3,z4,z112,z8,z6]),(0,[z111,z3,z4,z372,z8,z6]),(0,[z2,z3,z4,z836,z8,z6]),(0,[z2,z3,z5,z8,z829,z115]),(1,[z2,z3,z4,z737,z8])],[(0,[z2,z3,z4,z837,z8,z6]),(0,[z2,z483,z3,z4,z71,z8]),(0,[z3,z4,z5,z838,z8,z6]),(0,[z97,z3,z4,z5,z8,z83]),(0,[z146,z2,z4,z5,z759,z6]),(0,[z50,z2,z3,z5,z8,z115])],[(0,[z356,z297,z29,z5,z8,z6]),(0,[z2,z4,z5,z839,z8,z6]),(0,[z2,z242,z4,z5,z8,z44]),(0,[z840,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z841]),(0,[z2,z15,z4,z5,z759,z6]),(1,[z2,z3,z785,z8,z6]),(0,[z2,z3,z4,z117,z733,z5])],[(0,[z2,z3,z4,z5,z842,z6]),(0,[z2,z3,z4,z8,z843,z6]),(1,[z2,z3,z5,z723,z6])]],
   [[(0,[z2,z3,z844,z5,z8,z6]),(0,[z2,z4,z5,z8,z845,z6]),(0,[z0,z3,z4,z5,z656,z6]),(0,[z2,z4,z748,z5,z8,z6]),(0,[z2,z13,z4,z748,z8,z6]),(0,[z2,z3,z5,z8,z846,z6]),(1,[z2,z3,z5,z8,z829])],[(0,[z2,z3,z4,z60,z8,z6]),(0,[z1,z2,z3,z414,z137,z6])],[(0,[z2,z3,z4,z5,z847,z6]),(0,[z2,z3,z4,z5,z848,z6]),(0,[z2,z3,z4,z5,z8,z849]),(0,[z2,z3,z4,z5,z850,z6]),(0,[z249,z2,z4,z49,z8,z6]),(0,[z2,z3,z4,z5,z851,z6]),(0,[z3,z4,z5,z852,z8,z6]),(0,[z2,z15,z4,z63,z101,z6]),(0,[z853,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z854,z8,z6]),(0,[z356,z3,z398,z29,z5,z6]),(0,[z2,z855,z4,z5,z8,z6]),(0,[z2,z3,z4,z230,z100,z6]),(0,[z50,z2,z3,z345,z5,z8]),(0,[z856,z2,z3,z5,z8,z6]),(0,[z2,z3,z4,z5,z857,z6]),(0,[z2,z858,z4,z5,z8,z6]),(0,[z859,z2,z3,z4,z8,z6]),(0,[z2,z3,z114,z5,z38,z170])]],
   [[(0,[z19,z154,z4,z5,z8,z6]),(0,[z2,z3,z4,z8,z860,z6]),(0,[z2,z3,z4,z5,z8,z861]),(0,[z2,z3,z4,z5,z862,z6]),(0,[z2,z3,z4,z74,z8,z6]),(0,[z2,z3,z863,z5,z8,z6]),(0,[z2,z3,z4,z864,z8,z6]),(0,[z2,z3,z865,z4,z5,z8]),(0,[z2,z3,z866,z5,z8,z6]),(0,[z2,z3,z4,z5,z109,z51])],[(0,[z2,z867,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z868]),(0,[z2,z3,z157,z138,z5,z139])],[(0,[z2,z3,z4,z5,z8,z869]),(0,[z97,z4,z5,z8,z83,z190]),(0,[z2,z3,z4,z5,z870,z6]),(0,[z2,z871,z3,z4,z5,z6]),(0,[z872,z2,z3,z4,z5,z6]),(0,[z2,z873,z4,z5,z8,z6]),(0,[z2,z4,z5,z874,z8,z6]),(0,[z2,z875,z4,z5,z8,z6]),(0,[z2,z173,z3,z4,z100,z6]),(0,[z2,z173,z3,z4,z876,z6])],[(0,[z2,z3,z4,z5,z8,z877]),(0,[z2,z3,z4,z5,z8,z878]),(0,[z19,z772,z4,z5,z8,z6]),(0,[z2,z4,z5,z49,z8,z191]),(0,[z2,z106,z3,z4,z100,z6]),(0,[z879,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z414,z6,z51])]],
   [[(0,[z52,z283,z4,z325,z8,z6]),(0,[z2,z3,z880,z5,z8,z6]),(0,[z2,z3,z4,z881,z8,z6]),(0,[z2,z3,z4,z882,z8,z6]),(0,[z2,z3,z4,z5,z883,z8]),(0,[z2,z73,z4,z5,z133,z6]),(0,[z355,z2,z3,z4,z733,z5])],[(0,[z220,z3,z884,z5,z8,z6]),(0,[z3,z4,z5,z8,z724,z116]),(0,[z355,z2,z3,z4,z5,z642])],[(0,[z2,z3,z4,z5,z8,z885]),(0,[z2,z3,z4,z5,z886,z6]),(0,[z2,z73,z4,z5,z8,z6]),(0,[z146,z2,z4,z5,z147,z6]),(0,[z2,z3,z4,z5,z170,z39])],[(0,[z2,z772,z4,z5,z8,z6]),(0,[z2,z4,z5,z8,z6,z887])]],
   [[(0,[z2,z3,z4,z888,z5,z6]),(0,[z2,z3,z889,z5,z8,z6]),(0,[z2,z3,z4,z890,z8,z6]),(0,[z110,z2,z3,z4,z8,z6]),(0,[z2,z3,z4,z891,z8,z6]),(0,[z2,z3,z4,z892,z8,z6]),(0,[z893,z3,z4,z5,z8,z6]),(0,[z2,z4,z5,z147,z759,z6]),(0,[z2,z894,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z8,z895])],[(0,[z2,z3,z5,z8,z896,z6]),(0,[z897,z2,z3,z4,z5,z8]),(0,[z97,z2,z4,z5,z8,z190]),(0,[z2,z58,z4,z369,z8,z6]),(0,[z2,z4,z5,z347,z133,z6])],[(0,[z19,z2,z4,z5,z8,z486]),(0,[z2,z15,z4,z5,z101,z6]),(0,[z2,z3,z4,z5,z456,z6])]],
   [[(0,[z184,z2,z3,z4,z155,z6]),(0,[z449,z3,z4,z112,z8,z6]),(0,[z2,z3,z58,z785,z8,z6]),(0,[z2,z3,z4,z5,z876,z6]),(0,[z2,z3,z118,z4,z5,z51])],[(0,[z2,z3,z898,z5,z8,z6]),(0,[z2,z3,z398,z4,z71,z6]),(0,[z111,z3,z4,z838,z8,z6]),(0,[z89,z3,z4,z5,z48,z288]),(0,[z2,z4,z5,z304,z8,z39]),(0,[z2,z3,z4,z414,z8,z6])],[(0,[z220,z3,z172,z5,z8,z6]),(0,[z28,z2,z4,z71,z8,z6]),(0,[z2,z3,z4,z5,z899,z6]),(0,[z2,z3,z4,z8,z900,z6]),(0,[z2,z3,z4,z901,z8,z6])],[(0,[z2,z3,z4,z5,z8,z902]),(0,[z2,z903,z4,z5,z8,z6]),(0,[z2,z3,z4,z904,z8,z6]),(0,[z2,z3,z905,z5,z8,z6]),(0,[z2,z3,z4,z876,z100,z6])]],
   [[(0,[z3,z4,z838,z112,z8,z6]),(0,[z2,z272,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z906]),(0,[z2,z609,z3,z4,z117,z5]),(0,[z2,z3,z4,z5,z907,z8]),(0,[z2,z272,z58,z225,z8,z6]),(0,[z50,z2,z3,z4,z5,z170])],[(0,[z2,z3,z908,z5,z8,z6]),(0,[z909,z2,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z910]),(0,[z911,z3,z4,z5,z8,z6]),(1,[z2,z4,z748,z8,z6]),(0,[z2,z433,z4,z5,z8,z39]),(0,[z912,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z913]),(1,[z3,z884,z5,z8,z6]),(0,[z2,z3,z4,z914,z8,z6]),(0,[z2,z3,z4,z5,z8,z915]),(0,[z2,z3,z4,z5,z477,z51])],[(0,[z2,z3,z4,z5,z8,z486]),(0,[z2,z3,z4,z5,z8,z916]),(0,[z111,z3,z4,z135,z8,z6]),(0,[z2,z3,z4,z20,z8,z6]),(0,[z2,z3,z58,z489,z8,z6]),(0,[z2,z4,z369,z8,z100,z6])]],
   [[(0,[z356,z3,z29,z5,z8,z6]),(0,[z2,z3,z4,z917,z8,z6]),(0,[z2,z918,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z159])],[(0,[z52,z283,z4,z60,z8,z6]),(0,[z301,z2,z4,z5,z8,z39]),(0,[z2,z3,z4,z919,z8,z6]),(0,[z772,z283,z4,z5,z8,z6]),(0,[z2,z920,z4,z5,z8,z6]),(0,[z2,z3,z4,z921,z8,z6]),(1,[z2,z4,z5,z759,z6]),(0,[z2,z922,z4,z5,z8,z6]),(0,[z2,z3,z4,z923,z8,z6]),(0,[z2,z3,z4,z5,z133,z6])],[(0,[z28,z2,z4,z5,z8,z6]),(0,[z82,z3,z4,z5,z8,z116]),(0,[z98,z97,z4,z5,z8,z83]),(0,[z2,z4,z161,z748,z8,z6]),(0,[z2,z3,z4,z8,z924,z6])]],
   [[(0,[z154,z772,z4,z5,z8,z6]),(0,[z221,z2,z3,z4,z100,z6]),(0,[z89,z3,z4,z5,z48,z159]),(0,[z1,z2,z3,z5,z723,z6]),(0,[z50,z2,z3,z5,z580,z8])],[(0,[z2,z3,z925,z4,z5,z6]),(0,[z0,z3,z4,z47,z30,z6]),(0,[z2,z3,z4,z5,z8,z926]),(0,[z927,z3,z4,z5,z8,z6]),(0,[z2,z14,z4,z49,z8,z6]),(0,[z2,z3,z5,z785,z8,z6]),(0,[z2,z3,z4,z928,z8,z6]),(0,[z2,z3,z157,z5,z684,z6]),(0,[z2,z73,z4,z132,z8,z88])],[(0,[z2,z3,z929,z5,z8,z6]),(0,[z2,z3,z4,z930,z8,z6]),(0,[z2,z42,z3,z4,z5,z6]),(0,[z2,z15,z4,z5,z101,z490])],[(0,[z2,z3,z4,z5,z8,z931]),(0,[z3,z4,z884,z5,z8,z6]),(0,[z111,z2,z3,z4,z155,z6]),(0,[z2,z454,z3,z4,z117,z5]),(0,[z2,z3,z4,z5,z8,z932]),(0,[z2,z3,z4,z933,z8,z6])]],
   [[(0,[z3,z772,z4,z5,z8,z6]),(0,[z2,z3,z4,z934,z8,z6]),(0,[z2,z3,z4,z5,z8,z182]),(0,[z2,z13,z4,z354,z8,z6]),(0,[z2,z3,z4,z5,z935,z6])],[(0,[z2,z3,z4,z5,z936,z6]),(0,[z184,z3,z4,z387,z8,z6]),(0,[z2,z3,z4,z937,z5,z8]),(0,[z2,z938,z4,z5,z8,z6])],[(0,[z2,z4,z5,z8,z190,z6]),(0,[z2,z4,z297,z71,z8,z6]),(0,[z2,z4,z5,z8,z6,z939]),(0,[z2,z3,z4,z8,z940,z6]),(0,[z2,z3,z4,z199,z459,z6]),(0,[z2,z3,z4,z838,z8,z6]),(0,[z1,z2,z3,z4,z5,z288]),(0,[z2,z3,z4,z941,z8,z6]),(0,[z2,z3,z58,z225,z8,z6]),(0,[z2,z3,z4,z737,z8,z88])],[(0,[z2,z3,z4,z5,z8,z942]),(0,[z3,z4,z135,z838,z8,z6]),(0,[z2,z3,z4,z943,z8,z6]),(0,[z1,z2,z3,z18,z137,z6]),(0,[z399,z2,z3,z4,z5,z51]),(0,[z2,z3,z4,z199,z876,z6]),(0,[z2,z3,z4,z737,z8,z6]),(0,[z162,z2,z3,z4,z737,z8])]],
   [[(0,[z2,z3,z4,z944,z8,z6]),(0,[z2,z3,z4,z5,z155,z6]),(0,[z111,z3,z4,z135,z23,z6]),(0,[z3,z4,z5,z709,z48,z6]),(0,[z2,z3,z4,z63,z8,z490]),(0,[z2,z3,z4,z8,z876,z6])],[(0,[z2,z3,z4,z945,z8,z6]),(0,[z89,z3,z4,z5,z48,z6]),(0,[z2,z3,z4,z946,z8,z6]),(0,[z2,z3,z4,z5,z8,z947]),(0,[z948,z3,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z8,z949]),(0,[z89,z2,z3,z4,z30,z6]),(0,[z2,z13,z4,z161,z8,z6])],[(0,[z2,z4,z5,z8,z375,z39]),(0,[z2,z3,z4,z5,z8,z950]),(0,[z2,z951,z3,z4,z8,z6]),(0,[z2,z3,z4,z161,z155,z6]),(0,[z2,z3,z4,z5,z8,z724]),(0,[z2,z3,z4,z952,z8,z6]),(0,[z2,z4,z213,z49,z8,z6]),(0,[z953,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z170,z6]),(0,[z2,z4,z132,z347,z8,z88]),(0,[z2,z3,z4,z132,z737,z8])]],
   [[(0,[z2,z954,z3,z4,z8,z6]),(0,[z2,z3,z4,z955,z8,z6]),(0,[z2,z3,z4,z5,z956,z6]),(0,[z2,z294,z4,z161,z8,z6]),(0,[z2,z3,z4,z5,z957,z6]),(0,[z2,z3,z958,z5,z8,z6]),(0,[z2,z3,z556,z5,z8,z38]),(0,[z2,z3,z4,z785,z8,z6]),(0,[z2,z3,z688,z225,z8,z6])],[(0,[z2,z3,z4,z5,z8,z277]),(0,[z2,z3,z4,z959,z8,z6]),(0,[z2,z3,z4,z5,z960,z6]),(0,[z2,z961,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z962,z6]),(0,[z2,z3,z963,z5,z8,z6]),(0,[z2,z964,z4,z5,z8,z6]),(0,[z210,z2,z3,z4,z5,z6]),(0,[z50,z2,z3,z5,z8,z829])],[(0,[z2,z3,z965,z4,z5,z8]),(0,[z2,z3,z4,z966,z8,z6]),(0,[z2,z967,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z191]),(0,[z2,z3,z4,z5,z8,z829])],[(0,[z52,z151,z4,z5,z8,z6]),(0,[z2,z4,z297,z5,z8,z6]),(0,[z2,z3,z968,z4,z5,z8]),(0,[z2,z3,z4,z969,z8,z6]),(0,[z3,z4,z5,z47,z709,z6]),(0,[z2,z13,z4,z5,z8,z191]),(0,[z2,z3,z4,z5,z8,z970]),(0,[z2,z3,z4,z5,z971,z6]),(0,[z2,z4,z5,z972,z8,z6])]],
   [[(0,[z2,z3,z4,z5,z8,z973]),(0,[z2,z3,z4,z974,z5,z8]),(0,[z2,z3,z4,z5,z975,z6]),(0,[z976,z2,z3,z4,z5,z8]),(0,[z323,z2,z4,z5,z8,z44]),(0,[z3,z4,z5,z8,z6,z977])],[(0,[z110,z2,z42,z3,z4,z6]),(0,[z2,z3,z4,z5,z8,z978]),(0,[z2,z3,z4,z5,z8,z979]),(0,[z82,z3,z4,z5,z8,z724]),(0,[z2,z3,z4,z980,z8,z6]),(0,[z2,z3,z4,z132,z133,z88])],[(0,[z2,z981,z4,z5,z8,z6]),(0,[z110,z28,z2,z4,z8,z6]),(0,[z3,z172,z884,z5,z8,z6]),(0,[z2,z3,z4,z640,z100,z6]),(0,[z2,z58,z225,z369,z8,z6])],[(0,[z80,z3,z4,z5,z8,z116]),(0,[z2,z3,z4,z5,z8,z982]),(0,[z2,z3,z4,z199,z174,z6])]],
   [[(0,[z2,z3,z4,z983,z8,z6]),(0,[z984,z2,z3,z4,z5,z6]),(0,[z2,z4,z710,z5,z8,z6]),(0,[z2,z15,z4,z7,z101,z6]),(0,[z2,z3,z4,z733,z5,z109])],[(0,[z356,z3,z141,z29,z5,z8]),(0,[z2,z42,z3,z4,z71,z6]),(0,[z2,z3,z4,z5,z985,z6]),(0,[z2,z3,z4,z5,z986,z6]),(0,[z2,z987,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z490]),(0,[z2,z4,z988,z5,z8,z6])],[(0,[z356,z483,z3,z29,z5,z8]),(0,[z2,z989,z3,z4,z5,z6]),(0,[z89,z169,z3,z4,z5,z6]),(0,[z89,z3,z4,z5,z232,z6]),(0,[z2,z4,z5,z8,z712,z6])],[(0,[z2,z4,z5,z990,z8,z6]),(0,[z3,z4,z5,z991,z8,z6]),(0,[z2,z3,z4,z992,z8,z6]),(0,[z3,z4,z5,z8,z993,z6]),(0,[z2,z15,z4,z5,z101,z16])]],
   [[(0,[z2,z3,z4,z994,z8,z6]),(0,[z3,z884,z29,z5,z8,z6]),(0,[z2,z276,z4,z161,z8,z6]),(0,[z2,z3,z4,z5,z419,z51])],[(0,[z2,z42,z483,z3,z4,z5]),(0,[z97,z3,z4,z5,z8,z265])],[(0,[z2,z13,z4,z56,z8,z6]),(0,[z3,z4,z995,z5,z8,z6]),(0,[z2,z3,z5,z8,z38,z829]),(1,[z2,z3,z4,z876,z6])],[(0,[z2,z3,z5,z8,z996,z6]),(0,[z2,z3,z4,z997,z8,z6]),(0,[z2,z3,z4,z5,z8,z998]),(0,[z97,z3,z4,z291,z5,z8]),(0,[z2,z3,z5,z8,z6,z829]),(0,[z2,z3,z4,z174,z876,z6])]],
   [[(0,[z2,z3,z4,z5,z8,z999]),(0,[z2,z3,z4,z5,z1000,z6]),(0,[z2,z3,z4,z1001,z8,z6]),(0,[z0,z3,z4,z371,z5,z6]),(1,[z2,z710,z5,z8,z6]),(0,[z2,z710,z11,z5,z8,z6]),(0,[z2,z3,z4,z1002,z8,z6]),(0,[z2,z3,z4,z5,z1003,z6]),(0,[z355,z2,z3,z4,z414,z6])],[(0,[z2,z3,z884,z5,z8,z6]),(0,[z2,z1004,z3,z4,z5,z6]),(0,[z2,z302,z163,z129,z8,z6]),(0,[z2,z3,z4,z63,z8,z16]),(0,[z2,z3,z4,z5,z1005,z6]),(0,[z2,z3,z1006,z5,z8,z6])],[(0,[z2,z3,z4,z1007,z8,z6]),(0,[z2,z3,z4,z1008,z8,z6]),(0,[z2,z439,z4,z161,z8,z6]),(0,[z41,z2,z4,z5,z8,z44]),(0,[z2,z3,z4,z138,z5,z8]),(0,[z2,z73,z4,z5,z456,z6])],[(0,[z2,z3,z4,z5,z8,z1009]),(0,[z2,z3,z398,z4,z5,z6]),(0,[z2,z4,z5,z1010,z8,z6]),(0,[z2,z3,z4,z49,z155,z6]),(0,[z0,z3,z4,z5,z47,z6]),(0,[z2,z3,z4,z5,z8,z1011])]],
   [[(0,[z52,z2,z4,z5,z8,z191]),(0,[z2,z3,z4,z5,z1012,z6]),(0,[z19,z154,z4,z5,z8,z486]),(1,[z3,z4,z838,z8,z6]),(0,[z2,z3,z4,z748,z8,z6])],[(0,[z2,z3,z4,z1013,z8,z6]),(0,[z2,z398,z4,z297,z5,z6]),(0,[z2,z1014,z4,z5,z8,z6]),(0,[z2,z4,z606,z49,z8,z6]),(0,[z76,z2,z4,z369,z8,z6]),(0,[z2,z3,z4,z5,z8,z1015])],[(0,[z2,z163,z590,z5,z8,z6]),(0,[z356,z3,z884,z5,z8,z6]),(0,[z2,z3,z4,z1016,z8,z6]),(0,[z2,z3,z4,z1017,z8,z6]),(0,[z2,z302,z163,z20,z8,z6]),(0,[z2,z3,z4,z1018,z8,z6])],[(0,[z2,z3,z4,z5,z8,z1019]),(0,[z2,z1020,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z8,z1021]),(0,[z2,z3,z4,z5,z8,z1022]),(0,[z2,z3,z4,z5,z100,z288]),(0,[z2,z302,z710,z5,z8,z6]),(0,[z2,z3,z5,z8,z1023,z6]),(0,[z76,z2,z3,z380,z8,z6]),(0,[z2,z3,z4,z1024,z8,z6]),(0,[z2,z4,z199,z369,z8,z6]),(0,[z2,z3,z4,z733,z5,z6])]],
   [[(0,[z2,z4,z5,z1025,z8,z6]),(0,[z2,z1026,z4,z5,z8,z6]),(0,[z2,z4,z5,z347,z456,z6])],[(0,[z2,z4,z325,z8,z6,z39]),(0,[z110,z2,z3,z398,z4,z6]),(1,[z3,z4,z5,z8,z724]),(0,[z2,z4,z5,z369,z8,z6]),(0,[z2,z3,z4,z5,z759,z6]),(0,[z1,z2,z3,z4,z5,z386])],[(0,[z2,z3,z4,z5,z1027,z6]),(0,[z110,z2,z4,z297,z8,z6]),(0,[z2,z163,z4,z20,z8,z6]),(0,[z2,z427,z4,z5,z8,z44])],[(0,[z2,z3,z4,z7,z8,z6]),(0,[z2,z3,z4,z5,z1028,z6]),(0,[z41,z2,z4,z5,z8,z624])]],
   [[(0,[z2,z3,z4,z1029,z5,z8]),(0,[z2,z3,z4,z5,z8,z1030]),(0,[z2,z3,z4,z5,z8,z1031]),(0,[z2,z3,z4,z1032,z8,z6]),(0,[z2,z3,z785,z59,z8,z6]),(0,[z2,z3,z4,z1033,z8,z6])],[(0,[z2,z3,z4,z1034,z8,z6]),(0,[z2,z3,z1035,z5,z8,z6]),(0,[z184,z3,z4,z838,z8,z6]),(0,[z2,z1036,z4,z5,z8,z6]),(0,[z2,z3,z1037,z5,z8,z6]),(0,[z82,z2,z4,z5,z8,z190]),(0,[z2,z4,z117,z5,z8,z190])],[(0,[z1038,z2,z3,z5,z8,z6]),(0,[z2,z3,z4,z5,z1039,z6]),(0,[z10,z2,z11,z5,z8,z182]),(0,[z2,z3,z4,z5,z8,z16])],[(0,[z2,z3,z4,z5,z8,z1040]),(0,[z2,z3,z1041,z4,z5,z8]),(0,[z1042,z2,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z1043,z6]),(0,[z10,z2,z4,z20,z8,z6]),(0,[z2,z497,z4,z49,z8,z6])]],
   [[(0,[z1044,z2,z4,z5,z8,z6]),(0,[z2,z3,z4,z5,z8,z1045]),(0,[z0,z2,z3,z4,z30,z6]),(0,[z0,z2,z3,z4,z414,z6]),(0,[z10,z2,z11,z5,z8,z6]),(0,[z2,z3,z225,z785,z8,z6]),(0,[z1046,z3,z4,z5,z8,z6]),(0,[z2,z3,z5,z723,z137,z6]),(0,[z2,z1047,z4,z5,z8,z6])],[(0,[z2,z3,z4,z5,z1048,z6]),(0,[z2,z3,z4,z5,z1049,z6]),(0,[z2,z302,z163,z5,z8,z6]),(0,[z2,z3,z4,z1050,z8,z6])],[(0,[z2,z1051,z4,z5,z8,z6]),(0,[z672,z3,z4,z135,z8,z6]),(0,[z2,z3,z4,z8,z1052,z6])],[(0,[z2,z3,z4,z1053,z8,z6]),(0,[z110,z2,z483,z3,z4,z8]),(0,[z2,z3,z4,z5,z8,z288]),(0,[z2,z3,z4,z5,z174,z288]),(0,[z2,z3,z4,z5,z8,z1054]),(0,[z2,z3,z4,z5,z8,z1055]),(0,[z2,z3,z4,z1056,z8,z6]),(0,[z1057,z3,z4,z5,z8,z6]),(0,[z2,z3,z4,z199,z617,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 557) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 557).take 461) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1018)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [557, 461] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 99).take 29).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [99, 29] = true :=
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

end PEqualNP.Outside.L_meta_45868

theorem PEqualNP.Outside.L_meta_45868 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373472 * 2 ^ 32 + 4006127616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373472 * 2 ^ 32 + 4006127616) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45868.solve