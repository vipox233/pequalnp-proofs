import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38699

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
  Nat.testBit (4276808392 * 2 ^ 32 + 4272597504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8000484e18015556#64 ++ 0xa000121386005555#64 ++ 0x6c08f8fe3807ffff#64 ++ 0xdb023e3f8e01ffff#64 : BitVec 256),
   (0x04332322ee1b3330#64 ++ 0xc10cc8c8bb86cccc#64 ++ 0xe4772727fe3b3333#64 ++ 0xb91dc9c9ff8ecccc#64 : BitVec 256),
   (0x0985c5c746c3c3c3#64 ++ 0x02617171d1b0f0f0#64 ++ 0xfb87c7c7c7c3c3c3#64 ++ 0x7ee1f1f1f1f0f0f0#64 : BitVec 256),
   (0x02d807b0036c02a8#64 ++ 0x00b601ec00db00aa#64 ++ 0xfff807f807fc03fe#64 ++ 0xfffe01fe01ff00ff#64 : BitVec 256),
   (0x036fb00005b6a800#64 ++ 0x00dbec00016daa00#64 ++ 0xfffff80007fffc01#64 ++ 0xfffffe0001ffff00#64 : BitVec 256),
   (0x13fefefdb0000000#64 ++ 0x04ffbfbf6c000000#64 ++ 0xd3fffffff8000003#64 ++ 0xf4fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [7, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0248000001240000 0x0092000000490000 0xfff8000007fc0000 0xfffe000001ff0000

def z1 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff807f807fc03fe 0xfffe01fe01ff00ff

def z2 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe4772727fe3b3333 0xb91dc9c9ff8ecccc

def z3 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb87c7c7c7c3c3c3 0x7ee1f1f1f1f0f0f0

def z4 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd3fffffff8000003 0xf4fffffffe000000

def z5 : W := mkw 0x8000484e18015556 0xa000121386005555 0x000000fe380003fe 0x0000003f8e0000ff

def z6 : W := mkw 0x8000484e18015556 0xa000121386005555 0x6c08f8fe3807ffff 0xdb023e3f8e01ffff

def z7 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfffff80007fffc01 0xfffffe0001ffff00

def z8 : W := mkw 0x04332320e61a2220 0x410cc8c839868888 0x80770701c6380000 0x201dc1c0718e0000

def z9 : W := mkw 0x06fb27b2ef7f33b8 0xc1bec9ecbbdfccee 0xffff27ffffff33ff 0xffffc9ffffffccff

def z10 : W := mkw 0x04322322ea091330 0xc10c88c8ba8244cc 0xc0772727f8000333 0xb01dc9c9fe0000cc

def z11 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x24000000063b3330 0x09000000018ecccc

def z12 : W := mkw 0x8000080818001414 0xa000020206000505 0x0408383838043c3c 0x81020e0e0e010f0f

def z13 : W := mkw 0x04232002ec133110 0xc108c800bb04cc44 0x00072007f8033001 0x0001c801fe00cc00

def z14 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xff8fffffffc7ffff 0xffe3fffffff1ffff

def z15 : W := mkw 0x8905c84f5c83d557 0xa2417213d720f555 0x6c0ff8fff807ffff 0xdb03fe3ffe01ffff

def z16 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0x93870701c7c00000 0x24e1c1c071f00000

def z17 : W := mkw 0x13ccdcdd10000000 0x04f3373744000000 0x1388d8d800000000 0x44e2363600000000

def z18 : W := mkw 0x00322222a8011110 0x800c8888aa004444 0xe4772727f8033333 0xb91dc9c9fe00cccc

def z19 : W := mkw 0x1126f84db0000000 0x0449be136c000000 0x0007f807f8000001 0x0001fe01fe000000

def z20 : W := mkw 0x0984c4c500c0c0c3 0x0261313140303030 0x1b80c0c001c0c0c0 0x46e0303000703030

def z21 : W := mkw 0x127a3a38b0000000 0x049e8e8e2c000000 0x0078383838000000 0x801e0e0e0e000000

def z22 : W := mkw 0x02580230012c0028 0x0096008c004b000a 0x0070000000380000 0x001c0000000e0000

def z23 : W := mkw 0x109006b1a0000000 0x042401ac68000000 0x00000701c0000000 0x000001c070000000

def z24 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xa4770701c63b3330 0x291dc1c0718ecccc

def z25 : W := mkw 0x836ff84e1db7fd56 0xa0dbfe13876dff55 0xfffff8fe3fffffff 0xfffffe3f8fffffff

def z26 : W := mkw 0x0801010246c3c3c3 0x0200404091b0f0f0 0xe8070707c7c3c3c3 0x3a01c1c1f1f0f0f0

def z27 : W := mkw 0x84336b6efe1b7776 0xe10cdadbbf86dddd 0xec7ffffffe3fffff 0xfb1fffffff8fffff

def z28 : W := mkw 0x0905800144828001 0x024160005120a000 0x00070001c0000000 0x0001c00070000000

def z29 : W := mkw 0x0fffe7f7effff3fb 0xc3fff9fdfbfffcfe 0xffffe7fffffff3ff 0xfffff9fffffffcff

def z30 : W := mkw 0x10904efdb0000000 0x042413bf6c000000 0x000007fff8000002 0x000001fffe000000

def z31 : W := mkw 0x93fefeffb8015556 0xa4ffbfbfee005555 0xfffffffff807ffff 0xfffffffffe01ffff

def z32 : W := mkw 0x8beffdcf5ff7ffd7 0xa2fbff73d7fdfff5 0xffffffffffffffff 0xffffffffffffffff

def z33 : W := mkw 0x8423684efc137556 0xe108da13bf04dd55 0x6c0ff8fff807ffff 0xdb03fe3ffe01ffff

def z34 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x80772707fe3b3001 0x201dc9c1ff8ecc00

def z35 : W := mkw 0x0105800004828000 0x004160000120a000 0xfb87c00007c3c001 0x7ee1f00001f0f000

def z36 : W := mkw 0x036eb00000000000 0x00dbac0000000000 0x93f7000000000000 0x24fdc00000000000

def z37 : W := mkw 0x04332320e61a2220 0x410cc8c839868888 0xc0772727fe380003 0xb01dc9c9ff8e0000

def z38 : W := mkw 0x04332320e61a2220 0x410cc8c839868888 0xe4772701c63b3001 0xb91dc9c0718ecc00

def z39 : W := mkw 0x8000484c10004446 0x2000121304001111 0x4808f8fe3804cccf 0xd2023e3f8e013333

def z40 : W := mkw 0x13cc949100000000 0x04f3252440000000 0x1380000000000000 0x04e0000000000000

def z41 : W := mkw 0x0127b0000492a800 0x0049ec000124aa00 0x0007f8000003fc01 0x0001fe000000ff00

def z42 : W := mkw 0x03ffb7b007feaaa8 0x00ffedec01ffaaaa 0xfffffff807ffffff 0xfffffffe01ffffff

def z43 : W := mkw 0x13fefefdb1640088 0x04ffbfbf6c590022 0xdbfffffff9c400cf 0xf6fffffffe710033

def z44 : W := mkw 0x1527f84ffc133110 0xc549fe13ff04cc44 0x0007f807f8033001 0x0001fe01fe00cc00

def z45 : W := mkw 0x84104b6efa095776 0xe10412dbbe8255dd 0x000007fff80003fe 0x000001fffe0000ff

def z46 : W := mkw 0x03dcc6f500000000 0x00f731bd40000000 0xd3ffc7ffc0000003 0xf4fff1fff0000000

def z47 : W := mkw 0x0000484c10000000 0x0000121304000000 0x6c08f8fe3807fc03 0xdb023e3f8e01ff00

def z48 : W := mkw 0x02480100036c02a8 0x0092004000db00aa 0xfff8000007fc03fc 0xfffe000001ff00ff

def z49 : W := mkw 0x00322220a0000000 0x000c888828000000 0xc0772727f8000003 0xb01dc9c9fe000000

def z50 : W := mkw 0x0184cccd10000000 0x0061333344000000 0xd38ffffff8000003 0xf4e3fffffe000000

def z51 : W := mkw 0x0985c4c74483c143 0x02617131d120f050 0xd387c7c7c003c003 0x74e1f1f1f000f000

def z52 : W := mkw 0x8000000208015556 0xa000000082005555 0x2c0000000007fffc 0x0b0000000001ffff

def z53 : W := mkw 0x8985c5c74ec3d7d7 0xa2617171d3b0f5f5 0xff87c7c7c7c7ffff 0x7fe1f1f1f1f1ffff

def z54 : W := mkw 0x0010032002080220 0x000400c800820088 0xe470072006380332 0xb91c01c8018e00cc

def z55 : W := mkw 0x02c8049001640088 0x00b2012400590022 0x1b8800d801c400cc 0x46e2003600710033

def z56 : W := mkw 0x0001010246030300 0x000040409180c0c0 0xe0070707c6030303 0x3801c1c1f180c0c0

def z57 : W := mkw 0x04322220a8183030 0xc10c88882a060c0c 0x0470202038383030 0x811c08080e0e0c0c

def z58 : W := mkw 0x0984c4c500c0c0c3 0x0261313140303030 0xdb87c7c7c1c0c0c3 0x76e1f1f1f0703030

def z59 : W := mkw 0x00332320061a2220 0x000cc8c801868888 0xe4772720063b3333 0xb91dc9c8018ecccc

def z60 : W := mkw 0x0985c4c744c3c1c3 0x02617131d130f070 0x1b87c0c7c1c3c0c1 0x46e1f031f070f030

def z61 : W := mkw 0x14904ffffa091330 0xc52413fffe8244cc 0x000007fff8000332 0x000001fffe0000cc

def z62 : W := mkw 0x1bfffffff6c3c3c3 0x06fffffffdb0f0f0 0xfbffffffffc3c3c3 0xfefffffffff0f0f0

def z63 : W := mkw 0x0023200004122000 0x0008c80001048800 0xe4772000063b3001 0xb91dc800018ecc00

def z64 : W := mkw 0x034c900001a48800 0x00d3240000692200 0x1b88d80001c4cc00 0x46e2360000713300

def z65 : W := mkw 0x17ffb7b1e61a2220 0x45ffedec79868888 0x93f70701c6380000 0x24fdc1c0718e0000

def z66 : W := mkw 0x040101024fbfbb30 0xc100404093efeecc 0x2c00000007ffff30 0x0b00000001ffffcc

def z67 : W := mkw 0x077fb322efbfbb30 0xc1dfecc8bbefeecc 0xffffff27ffffff33 0xffffffc9ffffffcc

def z68 : W := mkw 0x03eef4c500000000 0x00fbbd3140000000 0xd3ffffc7c0000003 0xf4fffff1f0000000

def z69 : W := mkw 0x0beff5c747f7ebc3 0x02fbfd71d1fdfaf0 0xffffffc7c7ffffc3 0xfffffff1f1fffff0

def z70 : W := mkw 0x0185c4c504828000 0x006171314120a000 0xfb87c7c7c7c3c003 0x7ee1f1f1f1f0f000

def z71 : W := mkw 0x127a3a38b0000000 0x049e8e8e2c000000 0xc07f3f3ff8000003 0xb01fcfcffe000000

def z72 : W := mkw 0x00326a6cb0000000 0x000c9a9b2c000000 0xc07ffffff8000003 0xf01ffffffe000000

def z73 : W := mkw 0x0248000001240000 0x0092000000490000 0xfff800f807fc03fe 0xfffe003e01ff00ff

def z74 : W := mkw 0x03ffb7b007feaaa8 0x00ffedec01ffaaaa 0xffff07f807fc03fe 0xffffc1fe01ff00ff

def z75 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z76 : W := mkw 0x0081058246430380 0x002041609190c0e0 0xfb8707c7c7c303c3 0x7ee1c1f1f1f0c0f0

def z77 : W := mkw 0x04232000e4122000 0x4108c80039048800 0x00070001c0000000 0x0001c00070000000

def z78 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xf7f0072007f80332 0xbdfc01c801fe00cc

def z79 : W := mkw 0x13fefffdb36c02a8 0x04ffbfff6cdb00aa 0xfffffffffffc03ff 0xffffffffffff00ff

def z80 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xec7f27fffe3f33ff 0xfb1fc9ffff8fccff

def z81 : W := mkw 0x026a300001342800 0x009a8c00004d0a00 0x04783800003c3c00 0x811e0e00000f0f00

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c08f8000007fc01 0xdb023e000001ff00

def z83 : W := mkw 0x0db7e7e7eedbf3f3 0xc36df9f9fbb6fcfc 0xfff7e7e7fffbf3f3 0xfffdf9f9fffefcfc

def z84 : W := mkw 0x1bfefefdb0c0c0c3 0x06ffbfbf6c303030 0xdbfffffff9c0c0c3 0xf6fffffffe703030

def z85 : W := mkw 0x0000404600014142 0x0000101180005050 0x6800c0c60003c3c3 0x5a0030318000f0f0

def z86 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0x9bffd80007fccc00 0x66fff60001ff3300

def z87 : W := mkw 0x02580230012c0028 0x0096008c004b000a 0x04780038003c003c 0x811e000e000f000f

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c0800f8000403fe 0xdb02003e000100ff

def z89 : W := mkw 0x8000484e18015556 0xa000121386005555 0x0000f8063803fc01 0x00003e018e00ff00

def z90 : W := mkw 0x0bdd87b147ee82a9 0x02f761ec51fba0aa 0xffff07f9c7fc03fe 0xffffc1fe71ff00ff

def z91 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0x93f0070007f80000 0x24fc01c001fe0000

def z92 : W := mkw 0x0beff5c746c3c3c3 0x02fbfd71d1b0f0f0 0xfbffffc7c7c3c3c3 0xfefffff1f1f0f0f0

def z93 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xfb87c701c7c3c001 0x7ee1f1c071f0f000

def z94 : W := mkw 0x9126f84fb8015556 0xa449be13ee005555 0x6c0ff8fff807ffff 0xdb03fe3ffe01ffff

def z95 : W := mkw 0x14b36ffffe1b3330 0xc52cdbffff86cccc 0xe47727fffe3b3333 0xb91dc9ffff8ecccc

def z96 : W := mkw 0x00332322e6030300 0x000cc8c8b980c0c0 0xe0772727fe030303 0xb81dc9c9ff80c0c0

def z97 : W := mkw 0x0b6ff04745b7e943 0x02dbfc11d16dfa50 0xfffff807c7fffc01 0xfffffe01f1ffff00

def z98 : W := mkw 0x0023200004122000 0x0008c80001048800 0x8077000006380000 0x201dc000018e0000

def z99 : W := mkw 0x8000484e18015556 0xa000121386005555 0x0808d8fe3804cffe 0x4202363f8e0133ff

def z100 : W := mkw 0x80904ffe1a4957fe 0xa02413ff869255ff 0x6c08fffe3807ffff 0xdb023fff8e01ffff

def z101 : W := mkw 0x1136fa6db0000000 0x044dbe9b6c000000 0xc077ff27f8000003 0xb01dffc9fe000000

def z102 : W := mkw 0x02c8058003640280 0x00b2016000d900a0 0xfff807c007fc03c2 0xfffe01f001ff00f0

def z103 : W := mkw 0x0023200004122000 0x0008c80001048800 0xec7ff800063ffc01 0xfb1ffe00018fff00

def z104 : W := mkw 0x0104900000808800 0x0041240000202200 0x0000d8000000cc00 0x0000360000003300

def z105 : W := mkw 0x04332222ec1b3130 0xc10cc888bb06cc4c 0x04772027f83b3031 0x811dc809fe0ecc0c

def z106 : W := mkw 0x02fb27b0077e22a8 0x00bec9ec01df88aa 0xffff27f807ff33ff 0xffffc9fe01ffccff

def z107 : W := mkw 0x0db7a7a3eedbb3b1 0xc36de9e8fbb6ecec 0xf7f72727fffb3333 0xbdfdc9c9fffecccc

def z108 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xffff000007fc0000 0xffffc00001ff0000

def z109 : W := mkw 0x067a3220a93c3830 0xc19e8c882a4f0e0c 0x04783820383c3c30 0x811e0e080e0f0f0c

def z110 : W := mkw 0x8401494e5e1b7776 0xe10052539786dddd 0x6c08f8fe3e3fffff 0xdb023e3f8f8fffff

def z111 : W := mkw 0x0184c4c500000000 0x0061313140000000 0xd387c7c7c0000003 0x74e1f1f1f0000000

def z112 : W := mkw 0x000101024e031310 0x800040409380c4c4 0xe4072727fe033333 0xb901c9c9ff80cccc

def z113 : W := mkw 0x880101024ec3d7d7 0xa200404093b0f5f5 0x2c00000007c7fffc 0x0b00000001f1ffff

def z114 : W := mkw 0x02fa26b0a0000000 0x00be89ac28000000 0xd3ff27fff8000003 0xf4ffc9fffe000000

def z115 : W := mkw 0x00000100036c02a8 0x0000004000db00aa 0x0000000007f80000 0x0000000001fe0000

def z116 : W := mkw 0x12fa7efdb0000000 0x04be9fbf6c000000 0x00783ffff8000002 0x801e0ffffe000000

def z117 : W := mkw 0x036eb00000000000 0x00dbac0000000000 0xd3fff80000000001 0xf4fffe0000000000

def z118 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0x93f007f807f803fe 0x24fc01fe01fe00ff

def z119 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x93f707fff8000002 0x24fdc1fffe000000

def z120 : W := mkw 0x8000080810000404 0x2000020204000101 0x0008181800040c0c 0x0002060600010303

def z121 : W := mkw 0x8000484c10004446 0x2000121304001111 0x0808d8d80004cccc 0x4202363600013333

def z122 : W := mkw 0x8985cdcf56c3c7c7 0x22617373d5b0f1f1 0xfb8fdfdfc7c7cfcf 0x7ee3f7f7f1f1f3f3

def z123 : W := mkw 0x088045c7424143c3 0x02201171d09050f0 0x000007c7c00003c2 0x000001f1f00000f0

def z124 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0x93f7000007f80000 0x24fdc00001fe0000

def z125 : W := mkw 0x036fb00004122000 0x00dbec0001048800 0xf7fff800063b3001 0xfdfffe00018ecc00

def z126 : W := mkw 0x0985c5c546c2c2c3 0x0261717151b0b0b0 0x9b87c7c1c7c0c0c0 0x66e1f1f071f03030

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x0408380000043c00 0x81020e0000010f00

def z128 : W := mkw 0x0801010246c3c3c3 0x0200404091b0f0f0 0x2800000007c3c3c0 0x0a00000001f0f0f0

def z129 : W := mkw 0x13fffefdb5b6a800 0x04ffffbf6d6daa00 0xfffffffffffffc03 0xffffffffffffff00

def z130 : W := mkw 0x127a7a7cb0000000 0x049e9e9f2c000000 0x4078f8fe38000003 0xd01e3e3f8e000000

def z131 : W := mkw 0x04332322e61b2320 0x410cc8c8b986c8c8 0xe0770707c63b0303 0x381dc1c1f18ec0c0

def z132 : W := mkw 0x0905c0474483c143 0x02417011d120f050 0x0007c007c003c001 0x0001f001f000f000

def z133 : W := mkw 0x037eb220a0000000 0x00dfac8828000000 0xd3ffff27f8000003 0xf4ffffc9fe000000

def z134 : W := mkw 0x0c332322eedbf3f3 0xc30cc8c8bbb6fcfc 0xec772727fffbf3f3 0xbb1dc9c9fffefcfc

def z135 : W := mkw 0x10b26efdb0000000 0x042c9bbf6c000000 0xc07727fff8000003 0xb01dc9fffe000000

def z136 : W := mkw 0x0000000208011110 0x8000000082004444 0x6400202638033333 0x990008098e00cccc

def z137 : W := mkw 0x0248000001240000 0x0092000000490000 0x1b88000001c40000 0x46e2000000710000

def z138 : W := mkw 0x0185858006c28280 0x0061616001b0a0a0 0xfb87c7c007c3c3c3 0x7ee1f1f001f0f0f0

def z139 : W := mkw 0x80904ffe1a4957fe 0xa02413ff869255ff 0x000007fe380003fe 0x000001ff8e0000ff

def z140 : W := mkw 0x04100322ea091330 0xc10400c8ba8244cc 0x00000727f8000332 0x000001c9fe0000cc

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0070707c0000003 0x3001c1c1f0000000

def z142 : W := mkw 0x0985c5c74ec3d3d3 0x82617171d3b0f4f4 0xff87e7e7ffc3f3f3 0xffe1f9f9fff0fcfc

def z143 : W := mkw 0x0258023000000000 0x0096008c00000000 0x0078003800000000 0x801e000e00000000

def z144 : W := mkw 0x8000080818001414 0xa000020206000505 0x6c0838f838043ffe 0xdb020e3e0e010fff

def z145 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff8070007fc0000 0xfffe01c001ff0000

def z146 : W := mkw 0x036eb00000000000 0x00dbac0000000000 0xfffff8000007fc01 0xfffffe000001ff00

def z147 : W := mkw 0x90904effb8015556 0xa42413bfee005555 0x6c08fffff807ffff 0xdb023ffffe01ffff

def z148 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xfb87c7ffffc3c3ff 0x7ee1f1fffff0f0ff

def z149 : W := mkw 0x13fefeffb8011110 0x84ffbfbfee004444 0xf7fffffff8033333 0xfdfffffffe00cccc

def z150 : W := mkw 0x17ffffffff7f33b8 0xc5ffffffffdfccee 0xffffffffffff33ff 0xffffffffffffccff

def z151 : W := mkw 0x06fb27b0e77e22a8 0x41bec9ec39df88aa 0x93f70701c7f80000 0x24fdc1c071fe0000

def z152 : W := mkw 0x0127b00005b6a800 0x0049ec00016daa00 0x2c07f80007fffc01 0x0b01fe0001ffff00

def z153 : W := mkw 0x1248181810000000 0x0492060604000000 0x0008181800000000 0x0002060600000000

def z154 : W := mkw 0x0000000001640088 0x0000000000590022 0x0800000001c400cc 0x0200000000710033

def z155 : W := mkw 0x0080058002400280 0x00200160009000a0 0xfb8007c007c003c2 0x7ee001f001f000f0

def z156 : W := mkw 0x82d84ffe1b6d57fe 0xa0b613ff86db55ff 0xfff8fffe3fffffff 0xfffe3fff8fffffff

def z157 : W := mkw 0x04336b6efe1b3330 0xc10cdadbbf86cccc 0xe47ffffffe3b3333 0xf91fffffff8ecccc

def z158 : W := mkw 0x84332322ee1b7776 0xe10cc8c8bb86dddd 0xec772727fe3fffff 0xbb1dc9c9ff8fffff

def z159 : W := mkw 0x0bddc7f747efc3eb 0x02f771fdd1fbf0fa 0xffffc7ffc7ffc3ff 0xfffff1fff1fff0ff

def z160 : W := mkw 0x034d900005a68800 0x00d364000169a200 0xfb8fd80007c7cc01 0x7ee3f60001f1f300

def z161 : W := mkw 0x00222000a0000000 0x0008880028000000 0x00072007f8000001 0x0001c801fe000000

def z162 : W := mkw 0x17fffffffe1b3330 0xc5ffffffff86cccc 0xf7fffffffe3b3333 0xfdffffffff8ecccc

def z163 : W := mkw 0x18904ffff24143c3 0x062413fffc9050f0 0x000007fff80003c2 0x000001fffe0000f0

def z164 : W := mkw 0x009007b0024802a8 0x002401ec009200aa 0x000007f8000003fe 0x000001fe000000ff

def z165 : W := mkw 0x13fefffdb2080220 0x04ffbfff6c820088 0xf7fffffffe380333 0xfdffffffff8e00cc

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x6400002000000332 0x99000008000000cc

def z167 : W := mkw 0x8000404608015556 0xa000101182005555 0x6c00c0c60007ffff 0x5b0030318001ffff

def z168 : W := mkw 0x0010022000000000 0x0004008800000000 0xc070072000000002 0xb01c01c800000000

def z169 : W := mkw 0x067a2230a93c3038 0xc19e888c2a4f0c0e 0x04782038383c303c 0x811e080e0e0f0c0f

def z170 : W := mkw 0x03efb58007f6aa80 0x00fbed6001fdaaa0 0xffffffc007ffffc3 0xfffffff001fffff0

def z171 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfffff8f807ffffff 0xfffffe3e01ffffff

def z172 : W := mkw 0x04100220a8081030 0xc10400882a02040c 0x0000002038000030 0x000000080e00000c

def z173 : W := mkw 0x0000484c10000000 0x0000121304000000 0x4008f8fe38000003 0xd0023e3f8e000000

def z174 : W := mkw 0x13feb6b1a0000000 0x04ffadac68000000 0x93f70701c0000000 0x24fdc1c070000000

def z175 : W := mkw 0x8000484e18015556 0xa000121386005555 0x0000000638000000 0x000000018e000000

def z176 : W := mkw 0x0bdd87b147ee82a9 0x02f761ec51fba0aa 0x93f70701c7f80000 0x24fdc1c071fe0000

def z177 : W := mkw 0x04100322ea091330 0xc10400c8ba8244cc 0x64002727f8033333 0x990009c9fe00cccc

def z178 : W := mkw 0x0023200005b6a800 0x0008c800016daa00 0xec77200007fffc01 0xbb1dc80001ffff00

def z179 : W := mkw 0x036fb0020db7b910 0x80dbec00836dee44 0xfffff8263fffff33 0xfffffe098fffffcc

def z180 : W := mkw 0x840101024e1b7776 0xe10040409386dddd 0x2c000000063ffffc 0x0b000000018fffff

def z181 : W := mkw 0x04322220a0182020 0x410c888828060808 0x0070000000380000 0x001c0000000e0000

def z182 : W := mkw 0x13ccdcdd11a48800 0x04f3373744692200 0x1b88d8d801c4cc00 0x46e2363600713300

def z183 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff8fff807ffffff 0xfffe3ffe01ffffff

def z184 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xfffffffff807fc03 0xfffffffffe01ff00

def z185 : W := mkw 0x836ff84c15b6ec46 0x20dbfe13056dbb11 0xfffff8d807fffccd 0xfffffe3601ffff33

def z186 : W := mkw 0x0080048000400080 0x0020012000100020 0x1b8000c001c000c0 0x46e0003000700030

def z187 : W := mkw 0x04332220ac1a3030 0xc10cc8882b068c0c 0xe47720203e3b3031 0xb91dc8080f8ecc0c

def z188 : W := mkw 0x80104b6e1a095776 0xa00412db868255dd 0xec78fffe3e3fffff 0xfb1e3fff8f8fffff

def z189 : W := mkw 0x088145c746c3c3c3 0x02205171d1b0f0f0 0x280007c7c7c3c3c2 0x0a0001f1f1f0f0f0

def z190 : W := mkw 0x0985858346c38381 0x02616160d1b0e0e0 0xf3870707c7c30303 0x3ce1c1c1f1f0c0c0

def z191 : W := mkw 0x0105800004828000 0x004160000120a000 0x9387000007c00000 0x24e1c00001f00000

def z192 : W := mkw 0x0985858346c3c3c3 0x02616160d1b0f0f0 0xbb870701c7c3c3c0 0x2ee1c1c071f0f0f0

def z193 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0x047ff800003ffc01 0x811ffe00000fff00

def z194 : W := mkw 0x8000494e1b6d57fe 0xa000125386db55ff 0x6c08f8fe3fffffff 0xdb023e3f8fffffff

def z195 : W := mkw 0x037fb220a5b6a800 0x00dfec88296daa00 0xffffff27fffffc03 0xffffffc9ffffff00

def z196 : W := mkw 0x04b327a2ee5b33b0 0xc12cc9e8bb96ccec 0xfff727e7fffb33f3 0xfffdc9f9fffeccfc

def z197 : W := mkw 0x0105c0460483c142 0x004170118120f050 0xfb87c0c607c3c3c3 0x7ee1f03181f0f0f0

def z198 : W := mkw 0x00322220a0000000 0x000c888828000000 0x0070202038000000 0x801c08080e000000

def z199 : W := mkw 0x02fa27b0a36c02a8 0x00be89ec28db00aa 0xffff27fffffc03ff 0xffffc9ffffff00ff

def z200 : W := mkw 0x06fb27b0e77e22a8 0x41bec9ec39df88aa 0xffff07f9c7fc03fe 0xffffc1fe71ff00ff

def z201 : W := mkw 0x13dcdefd10000000 0x04f737bf44000000 0xd3f8dff800000002 0xf4fe37fe00000000

def z202 : W := mkw 0x00332220a4122000 0x000cc88829048800 0xe4772727fe3b3003 0xb91dc9c9ff8ecc00

def z203 : W := mkw 0x0001000004828000 0x000040000120a000 0x2800000007c3c000 0x0a00000001f0f000

def z204 : W := mkw 0x13ccdcdd11640088 0x04f3373744590022 0x1b88d8d801c400cc 0x46e2363600710033

def z205 : W := mkw 0x088044c5004040c3 0x0220113140101030 0x000000c0000000c0 0x0000003000000030

def z206 : W := mkw 0x1bcddddf56c3c3c3 0x06f37777d5b0f0f0 0xfb8fdfdfc7c3c3c3 0x7ee3f7f7f1f0f0f0

def z207 : W := mkw 0x0bcdc5d747e7c3cb 0x02f37175d1f9f0f2 0xfb8fc7dfc7c7c3cf 0x7ee3f1f7f1f1f0f3

def z208 : W := mkw 0x1537fb6ffe1b3330 0xc54dfedbff86cccc 0xe477ff27fe3b3333 0xb91dffc9ff8ecccc

def z209 : W := mkw 0x008045c6024143c2 0x00201171809050f0 0xfb80c7c607c3c3c3 0x7ee031f181f0f0f0

def z210 : W := mkw 0x1194cefdb0000000 0x046533bf6c000000 0xd387c7fff8000003 0x74e1f1fffe000000

def z211 : W := mkw 0x1127f84db492a800 0x0449fe136d24aa00 0x0007f807f803fc01 0x0001fe01fe00ff00

def z212 : W := mkw 0x10904efdb0000000 0x042413bf6c000000 0x4008fffff8000003 0xd0023ffffe000000

def z213 : W := mkw 0x0000000008001010 0x8000000002000404 0x0400202038003030 0x810008080e000c0c

def z214 : W := mkw 0x037fb23005bea828 0x00dfec8c016faa0a 0xfffff83807fffc3d 0xfffffe0e01ffff0f

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x040800380004003c 0x8102000e0001000f

def z216 : W := mkw 0x82d84ffc136c46ee 0x20b613ff04db11bb 0xfff8dff807fccffe 0xfffe37fe01ff33ff

def z217 : W := mkw 0x13fefeffb0014142 0x04ffbfbfec005050 0xfbfffffff803c3c3 0xfefffffffe00f0f0

def z218 : W := mkw 0x0080058002400280 0x00200160009000a0 0xff8807f807c403fe 0xffe201fe01f100ff

def z219 : W := mkw 0x13eefcddb0000000 0x04fbbf376c000000 0x138ff8dff8000001 0x44e3fe37fe000000

def z220 : W := mkw 0x0000404600014142 0x0000101180005050 0x6c08c0fe0007c3ff 0xdb02303f8001f0ff

def z221 : W := mkw 0x03ffb6b005b6a800 0x00ffedac016daa00 0xfffffff807fffc03 0xfffffffe01ffff00

def z222 : W := mkw 0x0beff5c747f7ebc3 0x02fbfd71d1fdfaf0 0xfbf7c7c7c7fbc3c3 0x7efdf1f1f1fef0f0

def z223 : W := mkw 0x026a300001342800 0x009a8c00004d0a00 0x6c78f800003ffc01 0xdb1e3e00000fff00

def z224 : W := mkw 0x11b6fefdb0000000 0x046dbfbf6c000000 0x0007fffff8000003 0x0001fffffe000000

def z225 : W := mkw 0x0184c5c502400280 0x00613171409000a0 0xfb87c7c7c7c003c3 0x7ee1f1f1f1f000f0

def z226 : W := mkw 0x8000484e18015556 0xa000121386005555 0x6c08f8063807fc01 0xdb023e018e01ff00

def z227 : W := mkw 0x00110322460b0320 0x000440c89182c0c8 0xe4770727c63b0333 0xb91dc1c9f18ec0cc

def z228 : W := mkw 0x127a3a38b12c0028 0x049e8e8e2c4b000a 0x04783838383c003c 0x811e0e0e0e0f000f

def z229 : W := mkw 0x19a7fdcff6c3c3c3 0x0669ff73fdb0f0f0 0xfb87ffc7ffc3c3c3 0x7ee1fff1fff0f0f0

def z230 : W := mkw 0x0400000008183030 0xc100000002060c0c 0x0400000000383030 0x01000000000e0c0c

def z231 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x640020263e3b3333 0x990008098f8ecccc

def z232 : W := mkw 0x00000100036c02a8 0x0000004000db00aa 0x2c00000007fc03fc 0x0b00000001ff00ff

def z233 : W := mkw 0x0d95c7e7eecbd3f3 0xc36571f9fbb2f4fc 0xfb87c7e7ffc3c3f3 0x7ee1f1f9fff0f0fc

def z234 : W := mkw 0x04322322ea193330 0xc10c88c8ba864ccc 0x04702727f8383332 0x811c09c9fe0e0ccc

def z235 : W := mkw 0x0001000005b6a800 0x00004000016daa00 0x0000000007f80000 0x0000000001fe0000

def z236 : W := mkw 0x1bfffefff483c143 0x06ffffbffd20f050 0xd3fffffff803c003 0xf4fffffffe00f000

def z237 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0x047807f8003c03fe 0x811e01fe000f00ff

def z238 : W := mkw 0x11a6fccdb0000000 0x0469bf336c000000 0xd387ffc7f8000003 0x74e1fff1fe000000

def z239 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0x93f7f80007fbfc01 0x24fdfe0001feff00

def z240 : W := mkw 0x0d85c5c74edbf3f3 0xc3617171d3b6fcfc 0xff87c7c7c7fbf3f3 0x7fe1f1f1f1fefcfc

def z241 : W := mkw 0x88804dcf5a4157d7 0xa2201373d69055f5 0x000007fff80003fe 0x000001fffe0000ff

def z242 : W := mkw 0x0001000005b6a800 0x00004000016daa00 0x6c08f80007fffc01 0xdb023e0001ffff00

def z243 : W := mkw 0x13fefefdb1a48800 0x04ffbfbf6c692200 0xdbfffffff9c4cc03 0xf6fffffffe713300

def z244 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xff8fffc7c7c7ffc3 0xffe3fff1f1f1fff0

def z245 : W := mkw 0x136ef84db0000000 0x04dbbe136c000000 0xd3fff807f8000001 0xf4fffe01fe000000

def z246 : W := mkw 0x089047f7424943eb 0x022411fdd09250fa 0x000007ffc00003fe 0x000001fff00000ff

def z247 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xfffffffff80403ff 0xfffffffffe0100ff

def z248 : W := mkw 0x040001024a091330 0xc1000040928244cc 0x0000000000000330 0x00000000000000cc

def z249 : W := mkw 0x0befb58147f6aa81 0x02fbed6051fdaaa0 0x93f70701c7f80000 0x24fdc1c071fe0000

def z250 : W := mkw 0x927a7a7eb8015556 0xa49e9e9fae005555 0x6c78f8fe3807ffff 0xdb1e3e3f8e01ffff

def z251 : W := mkw 0x0984848100c08081 0x0261212040302020 0x1380000001c00000 0x04e0000000700000

def z252 : W := mkw 0x0248000000000000 0x0092000000000000 0xd3f8000000000000 0xf4fe000000000000

def z253 : W := mkw 0x0023200004122000 0x0008c80001048800 0x0007200000033001 0x0001c8000000cc00

def z254 : W := mkw 0x8000484c10004446 0x2000121304001111 0x6c08d8f80004cffe 0xdb02363e000133ff

def z255 : W := mkw 0x0000000208011110 0x8000000082004444 0x6c08f8263807ff33 0xdb023e098e01ffcc

def z256 : W := mkw 0x02c8059003640288 0x00b2016400d900a2 0xfb8807d807c403ce 0x7ee201f601f100f3

def z257 : W := mkw 0x0bcdc5c747e7c3c3 0x02f37171d1f9f0f0 0xffffc7c7c7ffc3c3 0xfffff1f1f1fff0f0

def z258 : W := mkw 0x0984c5c502c0c2c3 0x0261317140b030b0 0xfb80c7c007c0c3c2 0x7ee031f001f030f0

def z259 : W := mkw 0x00322320a2080220 0x000c88c828820088 0xe4772727fe380333 0xb91dc9c9ff8e00cc

def z260 : W := mkw 0x042321024e1b3330 0xc108c8409386cccc 0xe4772000063b3331 0xb91dc800018ecccc

def z261 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0x3b80c0c007c3c3c0 0x4ee0303001f0f0f0

def z262 : W := mkw 0x8000000208015556 0xa000000082005555 0x000000000003fc00 0x000000000000ff00

def z263 : W := mkw 0x0985c5c747efc3eb 0x02617171d1fbf0fa 0xff87c7c7c7ffc3ff 0x7fe1f1f1f1fff0ff

def z264 : W := mkw 0x001003220a091330 0x800400c8828244cc 0xe47027263e3b3333 0xb91c09c98f8ecccc

def z265 : W := mkw 0x04322220a8183030 0xc10c88882a060c0c 0xc4772727f8383033 0xb11dc9c9fe0e0c0c

def z266 : W := mkw 0x0127b0000492a800 0x0049ec000124aa00 0xe477f800063bfc01 0xb91dfe00018eff00

def z267 : W := mkw 0x02c8049001640088 0x00b2012400590022 0x1380000001c00000 0x04e0000000700000

def z268 : W := mkw 0x02580230012c0028 0x0096008c004b000a 0xfff8003807fc003c 0xfffe000e01ff000f

def z269 : W := mkw 0x02d806b000000000 0x00b601ac00000000 0xd3f807f800000002 0xf4fe01fe00000000

def z270 : W := mkw 0x8000484c10004446 0x2000121304001111 0x0000d8000000cc00 0x0000360000003300

def z271 : W := mkw 0x13fefefdb12c0028 0x04ffbfbf6c4b000a 0xd7fffffff83c003f 0xf5fffffffe0f000f

def z272 : W := mkw 0x0248000001240000 0x0092000000490000 0xfff8f80007fffc01 0xfffe3e0001ffff00

def z273 : W := mkw 0x13fefefdb1342800 0x04ffbfbf6c4d0a00 0xd7fffffff83c3c03 0xf5fffffffe0f0f00

def z274 : W := mkw 0x9bfffffffec3d7d7 0xa6ffffffffb0f5f5 0xffffffffffc7ffff 0xfffffffffff1ffff

def z275 : W := mkw 0x8905c84f5c83d557 0xa2417213d720f555 0x0007f807f803fc01 0x0001fe01fe00ff00

def z276 : W := mkw 0x040101024f7f33b8 0xc100404093dfccee 0x2c00000007ff33fc 0x0b00000001ffccff

def z277 : W := mkw 0x127a3a38b1342800 0x049e8e8e2c4d0a00 0x04783838383c3c00 0x811e0e0e0e0f0f00

def z278 : W := mkw 0x0000484c10000000 0x0000121304000000 0x000000fe38000002 0x0000003f8e000000

def z279 : W := mkw 0x0d37e367ee9bf373 0xc34df8d9fba6fcdc 0xe477e727fe3bf333 0xb91df9c9ff8efccc

def z280 : W := mkw 0x17fefefdb8183030 0xc5ffbfbf6e060c0c 0xd7fffffff8383033 0xf5fffffffe0e0c0c

def z281 : W := mkw 0x8000484e18015556 0xa000121386005555 0x0808f8de3807fccd 0x42023e378e01ff33

def z282 : W := mkw 0x026b200005362000 0x009ac800014d8800 0xffff200007ff3001 0xffffc80001ffcc00

def z283 : W := mkw 0x04332322ef7f33b8 0xc10cc8c8bbdfccee 0xec772727ffff33ff 0xbb1dc9c9ffffccff

def z284 : W := mkw 0x034d800005a68000 0x00d360000169a000 0xffffc00007ffc001 0xfffff00001fff000

def z285 : W := mkw 0x8423684efc137556 0xe108da13bf04dd55 0x0007f807f803fc01 0x0001fe01fe00ff00

def z286 : W := mkw 0x03cc949001e48888 0x00f3252400792222 0x1b88d8d801c4cccc 0x46e2363600713333

def z287 : W := mkw 0x034c900001a48800 0x00d3240000692200 0x1380000001c00000 0x04e0000000700000

def z288 : W := mkw 0x8000000008001414 0xa000000002000505 0x0400000000043c3c 0x0100000000010f0f

def z289 : W := mkw 0x0080058002400280 0x00200160009000a0 0x000007c0000003c2 0x000001f0000000f0

def z290 : W := mkw 0x040100024c133110 0xc10040009304cc44 0x0000000000033000 0x000000000000cc00

def z291 : W := mkw 0x0010032002080220 0x000400c800820088 0xec7807f8063c03fe 0xfb1e01fe018f00ff

def z292 : W := mkw 0x07ffb7b2efffbbb8 0xc1ffedecbbffeeee 0xffffffffffffffff 0xffffffffffffffff

def z293 : W := mkw 0x04222000a8103010 0xc10888002a040c04 0x0000200038003000 0x000008000e000c00

def z294 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xfb8707c1c7c003c2 0x7ee1c1f071f000f0

def z295 : W := mkw 0x8000484e18015556 0xa000121386005555 0x2c08d8d80007fffc 0x4b0236360001ffff

def z296 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x00072727f8033333 0x0001c9c9fe00cccc

def z297 : W := mkw 0x0010022000080020 0x0004008800020008 0x0470002000380030 0x811c0008000e000c

def z298 : W := mkw 0x009007b0036c02a8 0x002401ec00db00aa 0x2c0007f807fc03fe 0x0b0001fe01ff00ff

def z299 : W := mkw 0x84336b6efe1b7776 0xe10cdadbbf86dddd 0xe47727fffe3b33ff 0xb91dc9ffff8eccff

def z300 : W := mkw 0x0000404400000000 0x0000101100000000 0x4000c0c600000003 0x5000303180000000

def z301 : W := mkw 0x036eb00001b4a800 0x00dbac00006d2a00 0x1ff8f80001fcfc00 0xc7fe3e00007f3f00

def z302 : W := mkw 0x076fb1024fbfbb30 0xc1dbec4093efeecc 0xfffff80007ffff31 0xfffffe0001ffffcc

def z303 : W := mkw 0x93fefefdb0004446 0x24ffbfbf6c001111 0xdbfffffff804cccf 0xf6fffffffe013333

def z304 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x93f7ff07f8000001 0x24fdffc1fe000000

def z305 : W := mkw 0x02d907b007feaaa8 0x00b641ec01ffaaaa 0xfff807f807fffffe 0xfffe01fe01ffffff

def z306 : W := mkw 0x84326a6eb8197576 0xe10c9a9bae065d5d 0x6c78f8fe383fffff 0xdb1e3e3f8e0fffff

def z307 : W := mkw 0x83fffffe1ffffffe 0xa0ffffff87ffffff 0xfffffffe3fffffff 0xffffffff8fffffff

def z308 : W := mkw 0x13feb6b1a0000000 0x04ffadac68000000 0xd3ffff01c0000001 0xf4ffffc070000000

def z309 : W := mkw 0x93fefefdb8001414 0xa4ffbfbf6e000505 0xd7fffffff8043c3f 0xf5fffffffe010f0f

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0xfb80000007c00000 0x7ee0000001f00000

def z311 : W := mkw 0x009007b0024802a8 0x002401ec009200aa 0x0000070000000000 0x000001c000000000

def z312 : W := mkw 0x02d907b2476f03a8 0x00b641ec91dbc0ea 0xffff07ffc7ff03ff 0xffffc1fff1ffc0ff

def z313 : W := mkw 0x088145c7464343c3 0x02205171d190d0f0 0xe00707c7c60303c3 0x3801c1f1f180c0f0

def z314 : W := mkw 0x03dd87b007ee82a8 0x00f761ec01fba0aa 0xffffc7f807ffc3ff 0xfffff1fe01fff0ff

def z315 : W := mkw 0x0001000005b6a800 0x00004000016daa00 0x2c00000007fffc00 0x0b00000001ffff00

def z316 : W := mkw 0x02d806b0016c00a8 0x00b601ac005b002a 0x1ff800f801fc00fc 0xc7fe003e007f003f

def z317 : W := mkw 0x8984cccd10c0c4c7 0x2261333344303131 0x1b88d8d801c4cccc 0x46e2363600713333

def z318 : W := mkw 0x0000484c10000000 0x0000121304000000 0x6c08f8fe380403ff 0xdb023e3f8e0100ff

def z319 : W := mkw 0x9126f84fb8015556 0xa449be13ee005555 0x0007f807f803fc01 0x0001fe01fe00ff00

def z320 : W := mkw 0x0da7e5c7eed3f3d3 0xc369f971fbb4fcf4 0xfb87e7c7ffc3f3c3 0x7ee1f9f1fff0fcf0

def z321 : W := mkw 0x12d84efdb0000000 0x04b613bf6c000000 0xd3f807fff8000002 0xf4fe01fffe000000

def z322 : W := mkw 0x13fefffdb2400280 0x04ffbfff6c9000a0 0xfbffffffffc003c3 0xfefffffffff000f0

def z323 : W := mkw 0x0537a322ee9bb330 0xc14de8c8bba6eccc 0xfff7e727fffbf333 0xfffdf9c9fffefccc

def z324 : W := mkw 0x077fb320e7beaa20 0x41dfecc839efaa88 0xffffff01c7fffc01 0xffffffc071ffff00

def z325 : W := mkw 0x036fb00004828000 0x00dbec000120a000 0xfbfff80007c3c001 0xfefffe0001f0f000

def z326 : W := mkw 0x036fb0000492a800 0x00dbec000124aa00 0xd3fff8000003fc01 0xf4fffe000000ff00

def z327 : W := mkw 0x0000404600014142 0x0000101180005050 0x000000c6000003c2 0x00000031800000f0

def z328 : W := mkw 0x077fb322ee1b3330 0xc1dfecc8bb86cccc 0xf7ffff27fe3b3333 0xfdffffc9ff8ecccc

def z329 : W := mkw 0x0985cdcf56c3c3c3 0x02617373d5b0f0f0 0xfb8fffffffc3c3c3 0xfee3fffffff0f0f0

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c0000000007fc00 0x0b0000000001ff00

def z331 : W := mkw 0x8db7efeffedbf7f7 0xe36dfbfbffb6fdfd 0xffffffffffffffff 0xffffffffffffffff

def z332 : W := mkw 0x0184848100000000 0x0061212040000000 0x93870701c0000000 0x24e1c1c070000000

def z333 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfbf007c007f803c2 0x7efc01f001fe00f0

def z334 : W := mkw 0x0904c0450080c043 0x0241301140203010 0x0000c0000000c000 0x0000300000003000

def z335 : W := mkw 0x0000404600014142 0x0000101180005050 0x6c08f8c60007ffc3 0xdb023e318001fff0

def z336 : W := mkw 0x8000000000004446 0x2000000000001111 0x080000000004cccc 0x0200000000013333

def z337 : W := mkw 0x0000000208011110 0x8000000082004444 0x6c0820fe380733ff 0xdb02083f8e01ccff

def z338 : W := mkw 0x0000000000000000 0x0000000000000000 0x6400200000033001 0x990008000000cc00

def z339 : W := mkw 0x13fffefdb5b6a800 0x04ffffbf6d6daa00 0xd3fffffffff80003 0xf4fffffffffe0000

def z340 : W := mkw 0x09b7e7e7e6c3c3c3 0x026df9f9f9b0f0f0 0xfbf7e7e7ffc3c3c3 0xfefdf9f9fff0f0f0

def z341 : W := mkw 0x0184c4c700014142 0x00613131c0005050 0xfb87c7c7c003c3c3 0x7ee1f1f1f000f0f0

def z342 : W := mkw 0x04000002e8011110 0xc1000000ba004444 0x00000007f8000000 0x00000001fe000000

def z343 : W := mkw 0x93fffeffbdb7fd56 0xa4ffffbfef6dff55 0xffffffffffffffff 0xffffffffffffffff

def z344 : W := mkw 0x02d807b20b6d13b8 0x80b601ec82db44ee 0xfff827fe3fff33ff 0xfffe09ff8fffccff

def z345 : W := mkw 0x0185c5c746030300 0x00617171d180c0c0 0xf387c7c7c6030303 0x7ce1f1f1f180c0c0

def z346 : W := mkw 0x8000484e18015556 0xa000121386005555 0x6c0800fe380403fe 0xdb02003f8e0100ff

def z347 : W := mkw 0x12fa3eb8b0000000 0x04be8fae2c000000 0xd3f83ff838000002 0xf4fe0ffe0e000000

def z348 : W := mkw 0x8000484e18015556 0xa000121386005555 0x6800c0fe3803c3ff 0x5a00303f8e00f0ff

def z349 : W := mkw 0x1bfffffdf6c28281 0x06ffffff7db0a0a0 0xd3ffffffffc00003 0xf4fffffffff00000

def z350 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xec7fff27fe3fff33 0xfb1fffc9ff8fffcc

def z351 : W := mkw 0x00322220a0000000 0x000c888828000000 0x80770701c0000000 0x201dc1c070000000

def z352 : W := mkw 0x13fefffdb36c02a8 0x04ffbfff6cdb00aa 0xd3fffffffff80003 0xf4fffffffffe0000

def z353 : W := mkw 0x09a7f5c746d3ebc3 0x0269fd71d1b4faf0 0xfb87ffc7c7c3ffc3 0x7ee1fff1f1f0fff0

def z354 : W := mkw 0x04332222ec133110 0xc10cc888bb04cc44 0xc0772727f8033003 0xb01dc9c9fe00cc00

def z355 : W := mkw 0x8000484c10004446 0x2000121304001111 0x000000d8000000cc 0x0000003600000033

def z356 : W := mkw 0x17fffefffc133110 0xc5ffffbfff04cc44 0xd3fffffff8033003 0xf4fffffffe00cc00

def z357 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xff8fc7ffc7c7c3ff 0xffe3f1fff1f1f0ff

def z358 : W := mkw 0x826a784e19357d56 0xa09a9e13864d5f55 0x6c78f8fe383fffff 0xdb1e3e3f8e0fffff

def z359 : W := mkw 0x02580330032c0228 0x009600cc00cb008a 0xe4780738063c033e 0xb91e01ce018f00cf

def z360 : W := mkw 0x034c900001a48800 0x00d3240000692200 0x7f88f80001c7fc01 0xdfe23e000071ff00

def z361 : W := mkw 0x8000484e18015556 0xa000121386005555 0x0408f83e3807fc3d 0x81023e0f8e01ff0f

def z362 : W := mkw 0x136ff84db5b6a800 0x04dbfe136d6daa00 0xfffff807fffffc01 0xfffffe01ffffff00

def z363 : W := mkw 0x8000484e18015556 0xa000121386005555 0x4008f8fe380003ff 0xd0023e3f8e0000ff

def z364 : W := mkw 0x8127f84e1c93fd56 0xa049fe138724ff55 0x0007f8063803fc01 0x0001fe018e00ff00

def z365 : W := mkw 0x0ad907b247efc3eb 0x02b641ec91fbf0fa 0xfff807f807ffc3fe 0xfffe01fe01fff0ff

def z366 : W := mkw 0x80804dce1a4157d6 0xa0201373869055f5 0xff88fffe3fc7ffff 0xffe23fff8ff1ffff

def z367 : W := mkw 0x84104b6efa095776 0xe10412dbbe8255dd 0x6c08fffff807ffff 0xdb023ffffe01ffff

def z368 : W := mkw 0x0000000200010100 0x0000000080004040 0x6000000600030303 0x180000018000c0c0

def z369 : W := mkw 0x02c80590036c02a8 0x00b2016400db00aa 0x3f8800d807fc03fc 0x4fe2003601ff00ff

def z370 : W := mkw 0x167b3b3afe1b3330 0xc59ececebf86cccc 0xe47f3f3ffe3b3333 0xb91fcfcfff8ecccc

def z371 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0x9bf807d807fc00cc 0x66fe01f601ff0033

def z372 : W := mkw 0x0ffff7e7effffbf3 0xc3fffdf9fbfffefc 0xffffffe7fffffff3 0xfffffff9fffffffc

def z373 : W := mkw 0x13ccdcdd10000000 0x04f3373744000000 0xd38fdfdfc0000003 0x74e3f7f7f0000000

def z374 : W := mkw 0x02d807b002080220 0x00b601ec00820088 0xf7f807f806380332 0xfdfe01fe018e00cc

def z375 : W := mkw 0x088045c7424143c3 0x02201171d09050f0 0xfb8007c7c7c003c2 0x7ee001f1f1f000f0

def z376 : W := mkw 0x08000102424143c3 0x02000040909050f0 0x00000000000003c0 0x00000000000000f0

def z377 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x93ffdfd9c0000000 0x64fff7f670000000

def z378 : W := mkw 0x0985c5c546c28281 0x0261717151b0a0a0 0xd387c7c7c7c00003 0x74e1f1f1f1f00000

def z379 : W := mkw 0x0bccc4d501e4c0cb 0x02f3313540793032 0x1b88c0d801c4c0cc 0x46e2303600713033

def z380 : W := mkw 0x10100a38b0000000 0x0404028e2c000000 0x0000003838000000 0x0000000e0e000000

def z381 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0x938707c7c7c003c2 0x24e1c1f1f1f000f0

def z382 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000f8000003fe 0x0000003e000000ff

def z383 : W := mkw 0x88804dcf5a4157d7 0xa2201373d69055f5 0x6c08fffff807ffff 0xdb023ffffe01ffff

def z384 : W := mkw 0x13feb7b1a36c02a8 0x04ffadec68db00aa 0xffff07f9c7fc03fe 0xffffc1fe71ff00ff

def z385 : W := mkw 0x00800580036c02a8 0x0020016000db00aa 0xff8007c007fc03fe 0x7fe001f001ff00ff

def z386 : W := mkw 0x036ff84c15b6a800 0x00dbfe13056daa00 0xfffff8fe3ffffc03 0xfffffe3f8fffff00

def z387 : W := mkw 0x82d807b20b6d57fe 0xa0b601ec82db55ff 0xfff807f807fffffe 0xfffe01fe01ffffff

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c08f8f80007ffff 0xdb023e3e0001ffff

def z389 : W := mkw 0x82584a7e192d557e 0xa096129f864b555f 0x6c78f8fe383fffff 0xdb1e3e3f8e0fffff

def z390 : W := mkw 0x036ef84c10000000 0x00dbbe1304000000 0xd3fff8fe38000003 0xf4fffe3f8e000000

def z391 : W := mkw 0x0105810246838300 0x0041604091a0e0c0 0xfb87c707c7c3c303 0x7ee1f1c1f1f0f0c0

def z392 : W := mkw 0x0881058246c3c3c3 0x0220416091b0f0f0 0xfb8007c007c3c3c2 0x7ee001f001f0f0f0

def z393 : W := mkw 0x8000484c10004446 0x2000121304001111 0x6c08f8d80007fccd 0xdb023e360001ff33

def z394 : W := mkw 0x026a300001342800 0x009a8c00004d0a00 0x0070000000380000 0x001c0000000e0000

def z395 : W := mkw 0x82d84ffe1b6d57fe 0xa0b613ff86db55ff 0xfff807fe3ffc03fe 0xfffe01ff8fff00ff

def z396 : W := mkw 0x0000404608015152 0x8000101182005454 0x6c00e0e63803f3f3 0xdb0038398e00fcfc

def z397 : W := mkw 0x90904effb8015556 0xa42413bfee005555 0x000007fff80003fe 0x000001fffe0000ff

def z398 : W := mkw 0x0000000208011110 0x8000000082004444 0x0000200638033001 0x000008018e00cc00

def z399 : W := mkw 0x02d847f6036d43ea 0x00b611fd80db50fa 0xfff8c7fe07ffc3ff 0xfffe31ff81fff0ff

def z400 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c08000000040000 0xdb02000000010000

def z401 : W := mkw 0x0beff4c505f6e8c3 0x02fbfd31417dba30 0xfffff8c007fffcc1 0xfffffe3001ffff30

def z402 : W := mkw 0x026b300005b6a800 0x009acc00016daa00 0x2c78380007fffc00 0x8b1e0e0001ffff00

def z403 : W := mkw 0x02d806b000000000 0x00b601ac00000000 0xfff807f8000403fe 0xfffe01fe000100ff

def z404 : W := mkw 0x0000010002000200 0x0000004000800080 0xe000070006000302 0x380001c0018000c0

def z405 : W := mkw 0x137efa7db0000000 0x04dfbe9f6c000000 0x007ff83ff8000001 0x801ffe0ffe000000

def z406 : W := mkw 0x167a3a38b8183030 0xc59e8e8e2e060c0c 0x0478383838383030 0x811e0e0e0e0e0c0c

def z407 : W := mkw 0x0105800005b6a800 0x00416000016daa00 0xff87c00007fffc01 0x7fe1f00001ffff00

def z408 : W := mkw 0x0010023000080028 0x0004008c0002000a 0x000000380000003c 0x0000000e0000000f

def z409 : W := mkw 0x0105800004828000 0x004160000120a000 0x0007c0000003c001 0x0001f0000000f000

def z410 : W := mkw 0x8bddcfff5fefd7ff 0xa2f773ffd7fbf5ff 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x0001010046020200 0x0000404011808080 0x80070701c6000000 0x2001c1c071800000

def z412 : W := mkw 0x0184c4c500000000 0x0061313140000000 0x1380c0c000000000 0x44e0303000000000

def z413 : W := mkw 0x8000000208015556 0xa000000082005555 0x6c0800f80007fffe 0xdb02003e0001ffff

def z414 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0x9387c707c7c3c001 0x24e1f1c1f1f0f000

def z415 : W := mkw 0x06d907b24f7f33b8 0xc1b641ec93dfccee 0xfff807f807ff33fe 0xfffe01fe01ffccff

def z416 : W := mkw 0x8023684e1c137556 0xa008da138704dd55 0xec7ff8fe3e3fffff 0xfb1ffe3f8f8fffff

def z417 : W := mkw 0x0ad847f7436d43eb 0x02b611fdd0db50fa 0xfff807ffc7fc03fe 0xfffe01fff1ff00ff

def z418 : W := mkw 0x0801414646c3c3c3 0x0200505191b0f0f0 0x6800c0c607c3c3c3 0x5a00303181f0f0f0

def z419 : W := mkw 0x0000000208011110 0x8000000082004444 0x0000002638000332 0x000000098e0000cc

def z420 : W := mkw 0x86fb6ffeff7f77fe 0xe1bedbffbfdfddff 0xffffffffffffffff 0xffffffffffffffff

def z421 : W := mkw 0x13feb6b1a0000000 0x04ffadac68000000 0xd3f72727f8000003 0xb4fdc9c9fe000000

def z422 : W := mkw 0x1126b001a0000000 0x0449ac0068000000 0x00070001c0000000 0x0001c00070000000

def z423 : W := mkw 0x1bccdcdd10c0c0c3 0x06f3373744303030 0x1b88d8d801c0c0c0 0x46e2363600703030

def z424 : W := mkw 0x037fb32007beaa20 0x00dfecc801efaa88 0xffffff2007ffff33 0xffffffc801ffffcc

def z425 : W := mkw 0x0537b322ee9bbb30 0xc14decc8bba6eecc 0xe477ff27fe3bff33 0xb91dffc9ff8effcc

def z426 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xfb87ffc7ffc3ffc3 0x7ee1fff1fff0fff0

def z427 : W := mkw 0x0001000004020000 0x0000400001008000 0xe007000006030001 0x3801c0000180c000

def z428 : W := mkw 0x008044c500000000 0x0020113140000000 0x000007c7c0000002 0x000001f1f0000000

def z429 : W := mkw 0x0905c1474683c343 0x02417051d1a0f0d0 0xe007c707c603c303 0x3801f1c1f180f0c0

def z430 : W := mkw 0x13fffffff6030300 0x04fffffffd80c0c0 0xf3fffffffe030303 0xfcffffffff80c0c0

def z431 : W := mkw 0x0001000004122000 0x0000400001048800 0x24000000063b3000 0x09000000018ecc00

def z432 : W := mkw 0x0527b002ec93b910 0xc149ec00bb24ee44 0x0007f807f803fc01 0x0001fe01fe00ff00

def z433 : W := mkw 0x067b3322ef3f3b30 0xc19eccc8bbcfcecc 0xe47f3f27fe3f3f33 0xb91fcfc9ff8fcfcc

def z434 : W := mkw 0x0cb367e7ee5b73f3 0xc32cd9f9fb96dcfc 0xe47727e7fe3b33f3 0xb91dc9f9ff8eccfc

def z435 : W := mkw 0x8184cccf18015556 0xa0613333c6005555 0xff8ffffff807ffff 0xffe3fffffe01ffff

def z436 : W := mkw 0x0905c14746c3c3c3 0x02417051d1b0f0f0 0x2807c007c7c3c3c1 0x0a01f001f1f0f0f0

def z437 : W := mkw 0x13feb7b1a36c02a8 0x04ffadec68db00aa 0x93f70701c7f80000 0x24fdc1c071fe0000

def z438 : W := mkw 0x00100220a0000000 0x0004008828000000 0x00000727f8000002 0x000001c9fe000000

def z439 : W := mkw 0x8000080818001414 0xa000020206000505 0x000000383800003c 0x0000000e0e00000f

def z440 : W := mkw 0x009006b000000000 0x002401ac00000000 0x000007f800000002 0x000001fe00000000

def z441 : W := mkw 0x0000000208011110 0x8000000082004444 0x2400000000033330 0x090000000000cccc

def z442 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000f8000003fc01 0x00003e000000ff00

def z443 : W := mkw 0x034d900005b6a800 0x00d36400016daa00 0x3f88d80007fffc00 0x4fe2360001ffff00

def z444 : W := mkw 0x0000484e18011110 0x8000121386004444 0x6408f8fe38033333 0xd9023e3f8e00cccc

def z445 : W := mkw 0x0105800004828000 0x004160000120a000 0xff8ff80007c7fc01 0xffe3fe0001f1ff00

def z446 : W := mkw 0x0126b00000000000 0x0049ac0000000000 0x0007f80000000001 0x0001fe0000000000

def z447 : W := mkw 0x93fefeffb8015556 0xa4ffbfbfee005555 0xd3fffffff80003ff 0xf4fffffffe0000ff

def z448 : W := mkw 0x0c0101024edbf3f3 0xc300404093b6fcfc 0x2c00000007fbf3f0 0x0b00000001fefcfc

def z449 : W := mkw 0x0800404740014143 0x02001011d0005050 0x00000007c0000000 0x00000001f0000000

def z450 : W := mkw 0x0001010007feaaa8 0x0000404001ffaaaa 0x2c00000007fffffc 0x0b00000001ffffff

def z451 : W := mkw 0x04322320aa183230 0xc10c88c82a860c8c 0xe47027203e383332 0xb91c09c80f8e0ccc

def z452 : W := mkw 0x06fa27b0ab7c32b8 0xc1be89ec2adf0cae 0xfff827f83ffc33fe 0xfffe09fe0fff0cff

def z453 : W := mkw 0x0801010046c28281 0x0200404011b0a0a0 0x0000000007c00000 0x0000000001f00000

def z454 : W := mkw 0x0000404600014142 0x0000101180005050 0x0000c0060003c001 0x000030018000f000

def z455 : W := mkw 0x0104800000808000 0x0041200000202000 0x1b80c00001c0c000 0x46e0300000703000

def z456 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0x1b8ff80001c7fc01 0x46e3fe000071ff00

def z457 : W := mkw 0x077fb320e7beaa20 0x41dfecc839efaa88 0x93f70701c7f80000 0x24fdc1c071fe0000

def z458 : W := mkw 0x01b6e6e5a0000000 0x006db9b968000000 0xd3f7e7e7f8000003 0xf4fdf9f9fe000000

def z459 : W := mkw 0x8984cccf18c1d5d7 0xa2613333c6307575 0x7f88f8fe39c7ffff 0xdfe23e3f8e71ffff

def z460 : W := mkw 0x0000010002080220 0x0000004000820088 0x2400000006380330 0x09000000018e00cc

def z461 : W := mkw 0x04336366ee1b7372 0xc10cd8d9bb86dcdc 0xec77e7e7fe3bf3f3 0xfb1df9f9ff8efcfc

def z462 : W := mkw 0x03efb49005f6a888 0x00fbed24017daa22 0xfffff8d807fffccd 0xfffffe3601ffff33

def z463 : W := mkw 0x04332320e61a2220 0x410cc8c839868888 0xe4770721c6380332 0xb91dc1c8718e00cc

def z464 : W := mkw 0x036eb00001a48800 0x00dbac0000692200 0xdbfff80001c4cc01 0xf6fffe0000713300

def z465 : W := mkw 0x03dcc7f5036c02a8 0x00f731fd40db00aa 0xffffc7ffc7fc03ff 0xfffff1fff1ff00ff

def z466 : W := mkw 0x04232102ee1b3330 0xc108c840bb86cccc 0x24072007fe3b3331 0x0901c801ff8ecccc

def z467 : W := mkw 0x0bddc7f746c3c3c3 0x02f771fdd1b0f0f0 0xfbffc7ffc7c3c3c3 0xfefff1fff1f0f0f0

def z468 : W := mkw 0x0022200000000000 0x0008880000000000 0xc077200000000001 0xb01dc80000000000

def z469 : W := mkw 0x8127f84e1c93fd56 0xa049fe138724ff55 0x6c0ff8fe3807ffff 0xdb03fe3f8e01ffff

def z470 : W := mkw 0x0248000001240000 0x0092000000490000 0x93f0000007f80000 0x24fc000001fe0000

def z471 : W := mkw 0x0995c7f746cbc3eb 0x026571fdd1b2f0fa 0xfb87c7ffc7c3c3ff 0x7ee1f1fff1f0f0ff

def z472 : W := mkw 0x0985c5c747f7ebc3 0x02617171d1fdfaf0 0xff87c7c7c7ffffc3 0x7fe1f1f1f1fffff0

def z473 : W := mkw 0x1927f84ff483c143 0x0649fe13fd20f050 0x0007f807f803c001 0x0001fe01fe00f000

def z474 : W := mkw 0x127a3230a0000000 0x049e8c8c28000000 0x0070000000000000 0x001c000000000000

def z475 : W := mkw 0x06fb27b2ef7f33b8 0xc1bec9ecbbdfccee 0xf7f72727fffb3333 0xbdfdc9c9fffecccc

def z476 : W := mkw 0x10804cdd10000000 0x0420133744000000 0x000000d800000000 0x0000003600000000

def z477 : W := mkw 0x0985c4c504c2c0c3 0x026171314130b030 0xfb87c0c007c3c0c1 0x7ee1f03001f0f030

def z478 : W := mkw 0x02d806b001240000 0x00b601ac00490000 0xfff807f807fc0002 0xfffe01fe01ff0000

def z479 : W := mkw 0x8000080a18015556 0xa000020286005555 0x2c0838383807fffc 0x8b020e0e0e01ffff

def z480 : W := mkw 0x1bfff7f7e6c3c3c3 0x06fffdfdf9b0f0f0 0xfbf7c7c7c7c3c3c3 0x7efdf1f1f1f0f0f0

def z481 : W := mkw 0x8000484c18005456 0xa000121306001515 0x0c08f8f83804fcfc 0xc3023e3e0e013f3f

def z482 : W := mkw 0x03eff4c505b6a800 0x00fbfd31416daa00 0xffffffc7c7fffc03 0xfffffff1f1ffff00

def z483 : W := mkw 0x02d806b0012c0028 0x00b601ac004b000a 0xd7f807f8003c003e 0xf5fe01fe000f000f

def z484 : W := mkw 0x8000080818001414 0xa000020206000505 0x6c08f8383807fc3d 0xdb023e0e0e01ff0f

def z485 : W := mkw 0x088045c7424143c3 0x02201171d09050f0 0x6800c7c7c003c3c3 0x5a0031f1f000f0f0

def z486 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xbff0070007fc03fc 0x2ffc01c001ff00ff

def z487 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0x0007c7c7c003c3c3 0x0001f1f1f000f0f0

def z488 : W := mkw 0x13fffffdb7feaaa8 0x04ffffff6dffaaaa 0xffffffffffffffff 0xffffffffffffffff

def z489 : W := mkw 0x80326a6eb8015556 0xa00c9a9bae005555 0xec7ffffff807ffff 0xfb1ffffffe01ffff

def z490 : W := mkw 0x0000080810000000 0x0000020204000000 0x0008383838000000 0x80020e0e0e000000

def z491 : W := mkw 0x0bcdd5c747e7cbc3 0x02f37571d1f9f2f0 0xfb8fdfc7c7c7cfc3 0x7ee3f7f1f1f1f3f0

def z492 : W := mkw 0x0248001001240008 0x0092000400490002 0x000800180004000c 0x0002000600010003

def z493 : W := mkw 0x10904ffdb24802a8 0x042413ff6c9200aa 0x000007fff80003fe 0x000001fffe0000ff

def z494 : W := mkw 0x0000484e10014142 0x0000121384005050 0x6808f8fe3803c3c3 0xda023e3f8e00f0f0

def z495 : W := mkw 0x0b6fb10247f7ebc3 0x02dbec4091fdfaf0 0xfffff80007ffffc1 0xfffffe0001fffff0

def z496 : W := mkw 0x17ffb7b3ee1b3330 0xc5ffedecfb86cccc 0xf7f72727fe3b3333 0xbdfdc9c9ff8ecccc

def z497 : W := mkw 0x076fb002edb7b910 0xc1dbec00bb6dee44 0xfffff807fffffc01 0xfffffe01ffffff00

def z498 : W := mkw 0x0801010247f7ebc3 0x0200404091fdfaf0 0x2c00000007ffffc0 0x0b00000001fffff0

def z499 : W := mkw 0x0001010246030300 0x000040409180c0c0 0x2000000006030300 0x080000000180c0c0

def z500 : W := mkw 0x93fefeffb8015556 0xa4ffbfbfee005555 0xd3fffffff803fc03 0xf4fffffffe00ff00

def z501 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0x1b8807f801c403fe 0x46e201fe007100ff

def z502 : W := mkw 0x067b2322ef3f3330 0xc19ec8c8bbcfcccc 0xffff2727ffff3333 0xffffc9c9ffffcccc

def z503 : W := mkw 0x04100322ea091330 0xc10400c8ba8244cc 0xe4700727fe380332 0xb91c01c9ff8e00cc

def z504 : W := mkw 0x82d80fb81b6c16bc 0xa0b603ee06db05af 0xfff83ff83ffc3ffe 0xfffe0ffe0fff0fff

def z505 : W := mkw 0x0248100001240800 0x0092040000490200 0x0008180000040c00 0x0002060000010300

def z506 : W := mkw 0x8000484e18015556 0xa000121386005555 0x2c0000fe3807fffe 0x0b00003f8e01ffff

def z507 : W := mkw 0x04b327b2ee5b33b8 0xc12cc9ecbb96ccee 0xe47727fffe3b33ff 0xb91dc9ffff8eccff

def z508 : W := mkw 0x0995c7e746cbc3e3 0x026571f9d1b2f0f8 0xfff7c7e7c7fbc3f3 0xfffdf1f9f1fef0fc

def z509 : W := mkw 0x02c8049000000000 0x00b2012400000000 0x138800d800000000 0x44e2003600000000

def z510 : W := mkw 0x836ff84e1db7fd56 0xa0dbfe13876dff55 0xfffff8063ffffc01 0xfffffe018fffff00

def z511 : W := mkw 0x02580320032c0220 0x009600c800cb0088 0xfff8072007fc0332 0xfffe01c801ff00cc

def z512 : W := mkw 0x0000010242010300 0x00000040908040c0 0x00000707c0000302 0x000001c1f00000c0

def z513 : W := mkw 0x836ef84e18015556 0xa0dbbe1386005555 0xfffff8fe3807ffff 0xfffffe3f8e01ffff

def z514 : W := mkw 0x0bdcc7f503ecc2eb 0x02f731fd40fb30ba 0xfff8c7f807fcc3fe 0xfffe31fe01ff30ff

def z515 : W := mkw 0x02580230012c0028 0x0096008c004b000a 0x6c7800f8003c03fe 0xdb1e003e000f00ff

def z516 : W := mkw 0x0905c0474483c143 0x02417011d120f050 0x6807c0c7c003c3c3 0x5a01f031f000f0f0

def z517 : W := mkw 0x84332b2afe1b3734 0xe10ccacabf86cdcd 0xe47f3f3ffe3f3f3f 0xb91fcfcfff8fcfcf

def z518 : W := mkw 0x04232002ec133110 0xc108c800bb04cc44 0xe4772007fe3b3001 0xb91dc801ff8ecc00

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008f80000000001 0xd0023e0000000000

def z520 : W := mkw 0x03feb6b000000000 0x00ffadac00000000 0xd3fffff800000003 0xf4fffffe00000000

def z521 : W := mkw 0x0010032002080220 0x000400c800820088 0x8070070006380000 0x201c01c0018e0000

def z522 : W := mkw 0x036eb00001342800 0x00dbac00004d0a00 0xd7fff800003c3c01 0xf5fffe00000f0f00

def z523 : W := mkw 0x0127b0000492a800 0x0049ec000124aa00 0xfb87f80007c3fc01 0x7ee1fe0001f0ff00

def z524 : W := mkw 0x8000484e18015556 0xa000121386005555 0x0000f8fe3803ffff 0x00003e3f8e00ffff

def z525 : W := mkw 0x8000484e18015556 0xa000121386005555 0x040838fe38043ffe 0x81020e3f8e010fff

def z526 : W := mkw 0x0000000001342800 0x00000000004d0a00 0x04000000003c3c00 0x01000000000f0f00

def z527 : W := mkw 0x0880058142400281 0x02200160509000a0 0x00000701c0000000 0x000001c070000000

def z528 : W := mkw 0x0080048000000000 0x0020012000000000 0xd38007c000000002 0x74e001f000000000

def z529 : W := mkw 0x877ffb6effbfff76 0xe1dffedbbfefffdd 0xffffffffffffffff 0xffffffffffffffff

def z530 : W := mkw 0x8000080a18011514 0xa000020286004545 0x6408383e38073f3f 0x99020e0f8e01cfcf

def z531 : W := mkw 0x927a3a38b8001414 0xa49e8e8e2e000505 0x0478383838043c3c 0x811e0e0e0e010f0f

def z532 : W := mkw 0x13fefffdb24802a8 0x04ffbfff6c9200aa 0xd3fffffff80003ff 0xf4fffffffe0000ff

def z533 : W := mkw 0x002320020c133110 0x8008c8008304cc44 0xe47720263e3b3333 0xb91dc8098f8ecccc

def z534 : W := mkw 0x17fefffffa091330 0xc5ffbffffe8244cc 0xd3fffffff8000333 0xf4fffffffe0000cc

def z535 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xf7f7200007fb3001 0xbdfdc80001fecc00

def z536 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x247020203e3b3330 0x891c08080f8ecccc

def z537 : W := mkw 0x13fefefdb1240000 0x04ffbfbf6c490000 0xfffffffffffc0003 0xffffffffffff0000

def z538 : W := mkw 0x17fffffdf61a2220 0x45ffffff7d868888 0xd3fffffffe380003 0xf4ffffffff8e0000

def z539 : W := mkw 0x036ff04605b7e942 0x00dbfc11816dfa50 0xfffff8c607ffffc3 0xfffffe3181fffff0

def z540 : W := mkw 0x0001000244030100 0x000040009100c040 0x00070007c0030001 0x0001c001f000c000

def z541 : W := mkw 0x82c84cdc116444ce 0x20b2133704591133 0x1b88d8d801c4cccc 0x46e2363600713333

def z542 : W := mkw 0x02fa37b0037c2aa8 0x00be8dec00df0aaa 0xfff83ff807fc3ffe 0xfffe0ffe01ff0fff

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c000000000403fc 0x0b000000000100ff

def z544 : W := mkw 0x82d84efe18015556 0xa0b613bf86005555 0xfff8fffe3807ffff 0xfffe3fff8e01ffff

def z545 : W := mkw 0x0984c5c742c1c3c3 0x02613171d0b070f0 0x1b80c7c7c1c0c3c2 0x46e031f1f07030f0

def z546 : W := mkw 0x1ffffffffedbf3f3 0xc7ffffffffb6fcfc 0xfffffffffffbf3f3 0xfffffffffffefcfc

def z547 : W := mkw 0x0befb58147f6aa81 0x02fbed6051fdaaa0 0xffffff01c7fffc01 0xffffffc071ffff00

def z548 : W := mkw 0x836fb8081db6bc14 0xa0dbee02076daf05 0xfffff8383ffffc3d 0xfffffe0e0fffff0f

def z549 : W := mkw 0x82c84cde196555de 0xa0b2133786595577 0x7f88f8fe39c7ffff 0xdfe23e3f8e71ffff

def z550 : W := mkw 0x0000484c10000000 0x0000121304000000 0x0000f80638000001 0x00003e018e000000

def z551 : W := mkw 0x1126f84db0000000 0x0449be136c000000 0x400ff8fff8000003 0xd003fe3ffe000000

def z552 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x80770727fe380332 0x201dc1c9ff8e00cc

def z553 : W := mkw 0x0801010247efc3eb 0x0200404091fbf0fa 0x2c00000007ffc3fc 0x0b00000001fff0ff

def z554 : W := mkw 0x0248000001240000 0x0092000000490000 0x04780000003c0000 0x811e0000000f0000

def z555 : W := mkw 0x009007b0024802a8 0x002401ec009200aa 0xe47007f8063803fe 0xb91c01fe018e00ff

def z556 : W := mkw 0x034c900000000000 0x00d3240000000000 0x1388d80000000000 0x44e2360000000000

def z557 : W := mkw 0x04332320ee1a3230 0xc10cc8c83b868c8c 0x84772721fe383030 0xa11dc9c87f8e0c0c

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0x680000c0000003c2 0x5a000030000000f0

def z559 : W := mkw 0x04010100461a2220 0x4100404011868888 0x0000000006380000 0x00000000018e0000

def z560 : W := mkw 0x1104d84d10000000 0x0441361344000000 0x0000d80000000000 0x0000360000000000

def z561 : W := mkw 0x13dcdefdb0000000 0x04f737bf6c000000 0x1388dffff8000002 0x44e237fffe000000

def z562 : W := mkw 0x8001484e1db7fd56 0xa0005213876dff55 0x6c08f8fe3fffffff 0xdb023e3f8fffffff

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000202638000003 0x900008098e000000

def z564 : W := mkw 0x04232002ec133110 0xc108c800bb04cc44 0x64072027f8033333 0x9901c809fe00cccc

def z565 : W := mkw 0x800100020db7fd56 0xa0004000836dff55 0x2c00000007fffffc 0x0b00000001ffffff

def z566 : W := mkw 0x8000484e18015556 0xa000121386005555 0x6800f8c63803ffc3 0x5a003e318e00fff0

def z567 : W := mkw 0x04110322ee0b1330 0xc10440c8bb82c4cc 0xe0070727fe030333 0x3801c1c9ff80c0cc

def z568 : W := mkw 0x13ffb6b1a5b6a800 0x04ffedac696daa00 0x93f70701c7f80000 0x24fdc1c071fe0000

def z569 : W := mkw 0x0127a0000492a000 0x0049e8000124a800 0xfff7e00007fbf001 0xfffdf80001fefc00

def z570 : W := mkw 0x00000100036c02a8 0x0000004000db00aa 0x6c0800f807fc03fe 0xdb02003e01ff00ff

def z571 : W := mkw 0x04100320e2080220 0x410400c838820088 0x00000701c0000000 0x000001c070000000

def z572 : W := mkw 0x1bffb7b1e6c28281 0x06ffedec79b0a0a0 0x93f70701c7c00000 0x24fdc1c071f00000

def z573 : W := mkw 0x036fb10247b7ab00 0x00dbec4091edeac0 0xffffff07c7ffff03 0xffffffc1f1ffffc0

def z574 : W := mkw 0x97fffffffe1b7776 0xe5ffffffff86dddd 0xfffffffffe3fffff 0xffffffffff8fffff

def z575 : W := mkw 0x02d807b002400280 0x00b601ec009000a0 0xfbf807f807c003c2 0xfefe01fe01f000f0

def z576 : W := mkw 0x0104c04500000000 0x0041301140000000 0x0007c007c0000001 0x0001f001f0000000

def z577 : W := mkw 0x02d807b0024802a8 0x00b601ec009200aa 0xd3f807f8000003fe 0xf4fe01fe000000ff

def z578 : W := mkw 0x0001414646034342 0x000050519180d0d0 0xe807c7c7c603c3c3 0x7a01f1f1f180f0f0

def z579 : W := mkw 0x077fb322efbfbb30 0xc1dfecc8bbefeecc 0xf7f72727fffb3333 0xbdfdc9c9fffecccc

def z580 : W := mkw 0x84322a28b8183434 0xe10c8a8a2e060d0d 0x04783838383c3c3c 0x811e0e0e0e0f0f0f

def z581 : W := mkw 0x8000000208015556 0xa000000082005555 0x00000000000003fc 0x00000000000000ff

def z582 : W := mkw 0x027a3230013c2828 0x009e8c8c004f0a0a 0x04783838003c3c3c 0x811e0e0e000f0f0f

def z583 : W := mkw 0x0000000000000000 0x0000000000000000 0x080800d8000400cc 0x4202003600010033

def z584 : W := mkw 0x09a7e5c746d3e3c3 0x0269f971d1b4f8f0 0xfff7e7c7c7fbf3c3 0xfffdf9f1f1fefcf0

def z585 : W := mkw 0x137eba38b0000000 0x04dfae8e2c000000 0xd3fff83838000001 0xf4fffe0e0e000000

def z586 : W := mkw 0x077fb220adbeb830 0xc1dfec882b6fae0c 0xfffff8203ffffc31 0xfffffe080fffff0c

def z587 : W := mkw 0x0db7e7e7e6dbe3e3 0x436df9f9f9b6f8f8 0xfbf7c7c7c7fbc3c3 0x7efdf1f1f1fef0f0

def z588 : W := mkw 0x000100000492a800 0x000040000124aa00 0x000000000003fc00 0x000000000000ff00

def z589 : W := mkw 0x0127b0000492a800 0x0049ec000124aa00 0x0007000000000000 0x0001c00000000000

def z590 : W := mkw 0x1bfefffff24143c3 0x06ffbffffc9050f0 0xd3fffffff80003c3 0xf4fffffffe0000f0

def z591 : W := mkw 0x8248484e19255556 0xa092121386495555 0xfff8f8fe3fffffff 0xfffe3e3f8fffffff

def z592 : W := mkw 0x0bfff7f747ffebeb 0x02fffdfdd1fffafa 0xffffffffc7ffffff 0xfffffffff1ffffff

def z593 : W := mkw 0x04332322efbfbb30 0xc10cc8c8bbefeecc 0xec772727ffffff33 0xbb1dc9c9ffffffcc

def z594 : W := mkw 0x0127b0000492a800 0x0049ec000124aa00 0x6c0ff8000007fc01 0xdb03fe000001ff00

def z595 : W := mkw 0x13ffb6b1a5b6a800 0x04ffedac696daa00 0xffffff01c7fffc01 0xffffffc071ffff00

def z596 : W := mkw 0x02d84efc10000000 0x00b613bf04000000 0xd3f8fffe38000003 0xf4fe3fff8e000000

def z597 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0xe4070707c63b3333 0x3901c1c1f18ecccc

def z598 : W := mkw 0x84336b6efe1b7776 0xe10cdadbbf86dddd 0xe477ff27fe3bff33 0xb91dffc9ff8effcc

def z599 : W := mkw 0x13fffefdb4828000 0x04ffffbf6d20a000 0xfbffffffffc3c003 0xfefffffffff0f000

def z600 : W := mkw 0x0000000001240000 0x0000000000490000 0x2c00000007fc0000 0x0b00000001ff0000

def z601 : W := mkw 0x0db7a7a1e6daa2a1 0x436de9e879b6a8a8 0x93f70701c7f80000 0x24fdc1c071fe0000

def z602 : W := mkw 0x03dc97b003ec8aa8 0x00f725ec00fb22aa 0xfff8dff807fccffe 0xfffe37fe01ff33ff

def z603 : W := mkw 0x0d27e047ec93f153 0xc349f811fb24fc54 0x0007e007f803f001 0x0001f801fe00fc00

def z604 : W := mkw 0x026b300005362800 0x009acc00014d8a00 0xe47f3800063f3c01 0xb91fce00018fcf00

def z605 : W := mkw 0x836fb0020db7fd56 0xa0dbec00836dff55 0xfffff80007fffffd 0xfffffe0001ffffff

def z606 : W := mkw 0x00000000012c0028 0x00000000004b000a 0x04000000003c003c 0x01000000000f000f

def z607 : W := mkw 0x0023210246132300 0x0008c8409184c8c0 0xe4772707c63b3303 0xb91dc9c1f18eccc0

def z608 : W := mkw 0x0249000005b6a800 0x00924000016daa00 0xfff8000007fffc00 0xfffe000001ffff00

def z609 : W := mkw 0x02d806b000000000 0x00b601ac00000000 0x93f0070000000000 0x24fc01c000000000

def z610 : W := mkw 0x93feffffbb6d57fe 0xa4ffbfffeedb55ff 0xffffffffffffffff 0xffffffffffffffff

def z611 : W := mkw 0x02d806b001640088 0x00b601ac00590022 0xdbf807f801c400ce 0xf6fe01fe00710033

def z612 : W := mkw 0x13febeb9b0000000 0x04ffafae6c000000 0x93ff3f39f8000000 0xa4ffcfce7e000000

def z613 : W := mkw 0x0905810246c3c3c3 0x0241604091b0f0f0 0xfb87c00007c3c3c1 0x7ee1f00001f0f0f0

def z614 : W := mkw 0x8000000208015556 0xa000000082005555 0x6c08f8000007fffd 0xdb023e000001ffff

def z615 : W := mkw 0x067b2332ef3f3338 0xc19ec8ccbbcfccce 0xe47f273ffe3f333f 0xb91fc9cfff8fcccf

def z616 : W := mkw 0x12d84ffdb36c02a8 0x04b613ff6cdb00aa 0xfff807fffffc03fe 0xfffe01ffffff00ff

def z617 : W := mkw 0x826a380819343c14 0xa09a8e02064d0f05 0x04783838383c3c3c 0x811e0e0e0e0f0f0f

def z618 : W := mkw 0x13effcdd15b6a800 0x04fbff37456daa00 0xfffff8d807fffc01 0xfffffe3601ffff00

def z619 : W := mkw 0x049007b2ea4913b8 0xc12401ecba9244ee 0x000007fff80003fe 0x000001fffe0000ff

def z620 : W := mkw 0x080100024483c143 0x020040009120f050 0x000000000003c000 0x000000000000f000

def z621 : W := mkw 0x8001494e5e035756 0xa00052539780d5d5 0xec0ffffffe07ffff 0xfb03ffffff81ffff

def z622 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xbff7000007fffc00 0x2ffdc00001ffff00

def z623 : W := mkw 0x0022300000102800 0x00088c0000040a00 0x0000380000003c00 0x00000e0000000f00

def z624 : W := mkw 0x0800000000c0c0c3 0x0200000000303030 0x0800000001c0c0c0 0x0200000000703030

def z625 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0x97f8073807fc003c 0xa5fe01ce01ff000f

def z626 : W := mkw 0x8000484e18015556 0xa000121386005555 0x6400f8263803ff33 0x99003e098e00ffcc

def z627 : W := mkw 0x009007b0024802a8 0x002401ec009200aa 0xfb8007f807c003fe 0x7ee001fe01f000ff

def z628 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfbf7c00007fbc001 0x7efdf00001fef000

def z629 : W := mkw 0x834cd84c11a4cc46 0x20d3361304693311 0x1b88d8d801c4cccc 0x46e2363600713333

def z630 : W := mkw 0x0010032002080220 0x000400c800820088 0x0000072000000332 0x000001c8000000cc

def z631 : W := mkw 0x0bddc7f747efc3eb 0x02f771fdd1fbf0fa 0xfbf7c7c7c7fbc3c3 0x7efdf1f1f1fef0f0

def z632 : W := mkw 0x0bccd4c501e4c8c3 0x02f3353140793230 0x1b88d8c001c4ccc0 0x46e2363000713330

def z633 : W := mkw 0x0000404400004042 0x0000101100001010 0x0800c0c00000c0c0 0x4200303000003030

def z634 : W := mkw 0x12fa3fb8b36c02a8 0x04be8fee2cdb00aa 0xfff83ff83ffc03fe 0xfffe0ffe0fff00ff

def z635 : W := mkw 0x13fffefdb4122000 0x04ffffbf6d048800 0xf7fffffffe3b3003 0xfdffffffff8ecc00

def z636 : W := mkw 0x834cd84e19a5dd56 0xa0d3361386697755 0x7f88f8fe39c7ffff 0xdfe23e3f8e71ffff

def z637 : W := mkw 0x02d84ffc136c02a8 0x00b613ff04db00aa 0xfff8fffe3ffc03ff 0xfffe3fff8fff00ff

def z638 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xd3f807f807f80002 0xf4fe01fe01fe0000

def z639 : W := mkw 0x17ffffffffbfbb30 0xc5ffffffffefeecc 0xffffffffffffff33 0xffffffffffffffcc

def z640 : W := mkw 0x036fb10007feaaa8 0x00dbec4001ffaaaa 0xfffff80007fffffd 0xfffffe0001ffffff

def z641 : W := mkw 0x0984c5c7424143c3 0x02613171d09050f0 0xd387c7c7c00003c3 0x74e1f1f1f00000f0

def z642 : W := mkw 0x8801494e5ec3d7d7 0xa200525397b0f5f5 0x6c08f8fe3fc7ffff 0xdb023e3f8ff1ffff

def z643 : W := mkw 0x13fffefdb492a800 0x04ffffbf6d24aa00 0xd3fffffff803fc03 0xf4fffffffe00ff00

def z644 : W := mkw 0x8000080818001414 0xa000020206000505 0x0000380038003c00 0x00000e000e000f00

def z645 : W := mkw 0x13fef6f5a0000000 0x04ffbdbd68000000 0xd3f7c7c7c0000003 0x74fdf1f1f0000000

def z646 : W := mkw 0x04232102ee133310 0xc108c840bb84ccc4 0xe0072707fe033303 0x3801c9c1ff80ccc0

def z647 : W := mkw 0x82580a38192c143c 0xa096028e064b050f 0x04783838383c3c3c 0x811e0e0e0e0f0f0f

def z648 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0x97ff380007fc3c00 0xa5ffce0001ff0f00

def z649 : W := mkw 0x026a300001342800 0x009a8c00004d0a00 0xfff8380007fc3c00 0xfffe0e0001ff0f00

def z650 : W := mkw 0x026a300000000000 0x009a8c0000000000 0x0078380000000000 0x801e0e0000000000

def z651 : W := mkw 0x02580330036c02a8 0x009600cc00db00aa 0x2c78003807fc03fc 0x8b1e000e01ff00ff

def z652 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xd3fff80007f80001 0xf4fffe0001fe0000

def z653 : W := mkw 0x034c900001a48800 0x00d3240000692200 0xfff8d80007fccc00 0xfffe360001ff3300

def z654 : W := mkw 0x1000484db0000000 0x040012136c000000 0x00000007f8000000 0x00000001fe000000

def z655 : W := mkw 0x8000484e18015556 0xa000121386005555 0x4008f8fe3803fc03 0xd0023e3f8e00ff00

def z656 : W := mkw 0x041103224e1b3330 0xc10440c89386cccc 0xe4700720063b3332 0xb91c01c8018ecccc

def z657 : W := mkw 0x0104800000000000 0x0041200000000000 0xd387c00000000001 0x74e1f00000000000

def z658 : W := mkw 0x1995cffff6c3c3c3 0x066573fffdb0f0f0 0xfb87c7ffffc3c3c3 0x7ee1f1fffff0f0f0

def z659 : W := mkw 0x03ffb7b007feaaa8 0x00ffedec01ffaaaa 0x93f7070007f80000 0x24fdc1c001fe0000

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0x0808d8000004cc00 0x4202360000013300

def z661 : W := mkw 0x02c8049001640088 0x00b2012400590022 0x7f8800f801c403fe 0xdfe2003e007100ff

def z662 : W := mkw 0x036eb00001240000 0x00dbac0000490000 0xfffff80007fc0001 0xfffffe0001ff0000

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800c0000003c001 0x5a0030000000f000

def z664 : W := mkw 0x0c9047e7ea4953f3 0xc32411f9fa9254fc 0x000007e7f80003f2 0x000001f9fe0000fc

def z665 : W := mkw 0x13dcdffd136c02a8 0x04f737ff44db00aa 0xfff8dff807fc03fe 0xfffe37fe01ff00ff

def z666 : W := mkw 0x0984c4c700c1c1c3 0x02613131c0307070 0x7b80c0c601c3c3c3 0x5ee030318070f0f0

def z667 : W := mkw 0x0080058002400280 0x00200160009000a0 0x9380070007c00000 0x24e001c001f00000

def z668 : W := mkw 0x13eefcdd10000000 0x04fbbf3744000000 0xd3fff8d800000001 0xf4fffe3600000000

def z669 : W := mkw 0x0080049000400088 0x0020012400100022 0x000000d8000000cc 0x0000003600000033

def z670 : W := mkw 0x0022200000102000 0x0008880000040800 0x0470200000383000 0x811c0800000e0c00

def z671 : W := mkw 0x0927f0474493e943 0x0249fc11d124fa50 0x0007f807c003fc01 0x0001fe01f000ff00

def z672 : W := mkw 0x00100320036c02a8 0x000400c800db00aa 0xec70072007fc03fe 0xbb1c01c801ff00ff

def z673 : W := mkw 0x10223808b0000000 0x04088e022c000000 0x0000380038000000 0x00000e000e000000

def z674 : W := mkw 0x04322222a8193130 0xc10c8888aa064c4c 0x64702026383b3333 0x991c08098e0ecccc

def z675 : W := mkw 0x93ccdcdd10004446 0x24f3373744001111 0x1b88d8d80004cccc 0x46e2363600013333

def z676 : W := mkw 0x06d807b2eb6d13b8 0xc1b601ecbadb44ee 0xfff807fffffc03fe 0xfffe01ffffff00ff

def z677 : W := mkw 0x03ffb7b007feaaa8 0x00ffedec01ffaaaa 0xffffff0007fffc01 0xffffffc001ffff00

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0xe470000006380000 0xb91c0000018e0000

def z679 : W := mkw 0x03feb7b0036c02a8 0x00ffadec00db00aa 0xfffffff807fc03ff 0xfffffffe01ff00ff

def z680 : W := mkw 0x8000484e10014546 0x2000121384005151 0x6808d8de0007cfcf 0x5a0236378001f3f3

def z681 : W := mkw 0x8000484c18001414 0xa000121306000505 0x4408f8fe38043c3f 0xd1023e3f8e010f0f

def z682 : W := mkw 0x0000484c10000000 0x0000121304000000 0x0008d8d800000000 0x4002363600000000

def z683 : W := mkw 0x93ccdcdf18015556 0xa4f33737c6005555 0x7f88f8fe3807ffff 0xdfe23e3f8e01ffff

def z684 : W := mkw 0x009007a0024802a0 0x002401e8009200a8 0xfff007e007f803f2 0xfffc01f801fe00fc

def z685 : W := mkw 0x8000000208015556 0xa000000082005555 0x6c0020263807ffff 0x9b0008098e01ffff

def z686 : W := mkw 0x13ccdcdd10000000 0x04f3373744000000 0x5388f8fe38000003 0xd4e23e3f8e000000

def z687 : W := mkw 0x137fba38b5b6a800 0x04dfee8e2d6daa00 0xfffff8383ffffc01 0xfffffe0e0fffff00

def z688 : W := mkw 0x0905c0474483c143 0x02417011d120f050 0xfb87c007c7c3c001 0x7ee1f001f1f0f000

def z689 : W := mkw 0x1bfffffff7efc3eb 0x06fffffffdfbf0fa 0xffffffffffffc3ff 0xfffffffffffff0ff

def z690 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x13f8f8f838000000 0xc4fe3e3e0e000000

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x400800f800000002 0xd002003e00000000

def z692 : W := mkw 0x05b7e7e7ee1b3330 0xc16df9f9fb86cccc 0xf7f7e7e7fe3b3333 0xfdfdf9f9ff8ecccc

def z693 : W := mkw 0x0000000200014142 0x0000000080005050 0x280000000003c3c0 0x0a0000000000f0f0

def z694 : W := mkw 0x8105c84e1c83d556 0xa04172138720f555 0xff8ff8fe3fc7ffff 0xffe3fe3f8ff1ffff

def z695 : W := mkw 0x04110322ee1b3330 0xc10440c8bb86cccc 0x24000727fe3b3332 0x090001c9ff8ecccc

def z696 : W := mkw 0x0000010002400280 0x00000040009000a0 0x2800000007c003c0 0x0a00000001f000f0

def z697 : W := mkw 0x13feb6b1a0000000 0x04ffadac68000000 0xd3ff07f9c0000002 0xf4ffc1fe70000000

def z698 : W := mkw 0x02c8049001640088 0x00b2012400590022 0xfff800d807fc00cc 0xfffe003601ff0033

def z699 : W := mkw 0x8000484e18015556 0xa000121386005555 0x2c00f8063807fffd 0x0b003e018e01ffff

def z700 : W := mkw 0x0000000001a48800 0x0000000000692200 0x0800000001c4cc00 0x0200000000713300

def z701 : W := mkw 0x8000484e18015556 0xa000121386005555 0x640020fe380333ff 0x9900083f8e00ccff

def z702 : W := mkw 0x00000100024802a8 0x00000040009200aa 0x00000000000003fc 0x00000000000000ff

def z703 : W := mkw 0x1bfffffff7f7ebc3 0x06fffffffdfdfaf0 0xffffffffffffffc3 0xfffffffffffffff0

def z704 : W := mkw 0x06fb27b2ee1b3330 0xc1bec9ecbb86cccc 0xf7ff27fffe3b3333 0xfdffc9ffff8ecccc

def z705 : W := mkw 0x800001020b6d57fe 0xa000004082db55ff 0x2c00000007fffffc 0x0b00000001ffffff

def z706 : W := mkw 0x009007b0024802a8 0x002401ec009200aa 0x6c0807f8000403fe 0xdb0201fe000100ff

def z707 : W := mkw 0x0184cccd10000000 0x0061333344000000 0xd387c7fff8000003 0x74e1f1fffe000000

def z708 : W := mkw 0x0d8585834edbb3b1 0xc3616160d3b6ecec 0xb7870701c7fb3330 0x2de1c1c071fecccc

def z709 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xfffffffff8040003 0xfffffffffe010000

def z710 : W := mkw 0x0185858246c38380 0x0061616091b0e0e0 0xfb87c7c7c7c3c3c3 0x7ee1f1f1f1f0f0f0

def z711 : W := mkw 0x0985c5c746cbc3eb 0x02617171d1b2f0fa 0xfb87c7c7c7c3c3ff 0x7ee1f1f1f1f0f0ff

def z712 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x00000000063b3000 0x00000000018ecc00

def z713 : W := mkw 0x075c9322ebad9b30 0xc1d724c8baeb66cc 0x1b88df27f9c4cf32 0x46e237c9fe7133cc

def z714 : W := mkw 0x027a2230a0000000 0x009e888c28000000 0xc07f273ff8000003 0xb01fc9cffe000000

def z715 : W := mkw 0x127a3a38b12c0028 0x049e8e8e2c4b000a 0x0078383838380000 0x801e0e0e0e0e0000

def z716 : W := mkw 0x836ff84e1db7fd56 0xa0dbfe13876dff55 0x93f700fe3ff803fe 0x24fdc03f8ffe00ff

def z717 : W := mkw 0x067a2232a93d3138 0xc19e888caa4f4c4e 0x6c7820fe383f33ff 0xdb1e083f8e0fccff

def z718 : W := mkw 0x84332322ee1b7776 0xe10cc8c8bb86dddd 0xe4772727fe3bff33 0xb91dc9c9ff8effcc

def z719 : W := mkw 0x13ccdcdd11640088 0x04f3373744590022 0x1388d8d801c00000 0x44e2363600700000

def z720 : W := mkw 0x04322220a0182020 0x410c888828060808 0xc0772727f8380003 0xb01dc9c9fe0e0000

def z721 : W := mkw 0x02fa26b0a1640088 0x00be89ac28590022 0xdbff27fff9c400cf 0xf6ffc9fffe710033

def z722 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xff87c7e7c7c3c3f3 0xffe1f1f9f1f0f0fc

def z723 : W := mkw 0x02d817b0036c0aa8 0x00b605ec00db02aa 0xfff81ff807fc0ffe 0xfffe07fe01ff03ff

def z724 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xd387c7c7c7c3c003 0x74e1f1f1f1f0f000

def z725 : W := mkw 0x8984cccd10c0c4c7 0x2261333344303131 0xdb8ffffff9c4cccf 0xf6e3fffffe713333

def z726 : W := mkw 0x01b6a6a1a0000000 0x006da9a868000000 0xd3f72727f8000003 0xb4fdc9c9fe000000

def z727 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xfb870701c7c00000 0x7ee1c1c071f00000

def z728 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfffff80007fffffd 0xfffffe0001ffffff

def z729 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0x9bf807f807fc03fe 0x66fe01fe01ff00ff

def z730 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x93ffdffff8000002 0x64fff7fffe000000

def z731 : W := mkw 0x037eb220a1a48800 0x00dfac8828692200 0xdbffff27f9c4cc03 0xf6ffffc9fe713300

def z732 : W := mkw 0x00326a6cb0000000 0x000c9a9b2c000000 0xc07727fff8000003 0xb01dc9fffe000000

def z733 : W := mkw 0x0984c4c500c08081 0x0261313140302020 0xd387c7c7c1c00003 0x74e1f1f1f0700000

def z734 : W := mkw 0x0985c5c746d3ebc3 0x02617171d1b4faf0 0xfb87c7c7c7c3ffc3 0x7ee1f1f1f1f0fff0

def z735 : W := mkw 0x00322220a0000000 0x000c888828000000 0xc07fff27f8000003 0xf01fffc9fe000000

def z736 : W := mkw 0x8985c5c746c3c7c7 0x22617171d1b0f1f1 0xfb87c7c7c7c7cfcf 0x7ee1f1f1f1f1f3f3

def z737 : W := mkw 0x027a3220a1342800 0x009e8c88284d0a00 0x04783820383c3c00 0x811e0e080e0f0f00

def z738 : W := mkw 0x17cddddf5e1b3330 0xc5f37777d786cccc 0x3788d8d8063b3330 0x4de23636018ecccc

def z739 : W := mkw 0x1a7b3b3af6c3c3c3 0x069ececebdb0f0f0 0x287838383fc3c3c0 0x8a1e0e0e0ff0f0f0

def z740 : W := mkw 0x13eefccdb0000000 0x04fbbf336c000000 0xd3ffffc7f8000003 0xf4fffff1fe000000

def z741 : W := mkw 0x13fefefdb0400080 0x04ffbfbf6c100020 0xdbfffffff9c000c3 0xf6fffffffe700030

def z742 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xff8f07f9c7c403fe 0xffe3c1fe71f100ff

def z743 : W := mkw 0x13fefefdb1240000 0x04ffbfbf6c490000 0xfffffffffffffc03 0xffffffffffffff00

def z744 : W := mkw 0x0985c4c744c3c1c3 0x02617131d130f070 0xdb87c7c7c1c3c0c3 0x76e1f1f1f070f030

def z745 : W := mkw 0x17fefefdb0182020 0x45ffbfbf6c060808 0xd3fffffff8380003 0xf4fffffffe0e0000

def z746 : W := mkw 0x00322220a0102000 0x000c888828040800 0xc4772727f8383003 0xb11dc9c9fe0e0c00

def z747 : W := mkw 0x8985cdcf56c3c7c7 0x22617373d5b0f1f1 0xfb87dfc7c7c3cfc3 0x7ee1f7f1f1f0f3f0

def z748 : W := mkw 0x13feb6b1a0000000 0x04ffadac68000000 0x93f72707f8000001 0x24fdc9c1fe000000

def z749 : W := mkw 0x8d85cdcf5edbf7f7 0xe3617373d7b6fdfd 0xff8fffffffffffff 0xffe3ffffffffffff

def z750 : W := mkw 0x1194cefdb0000000 0x046533bf6c000000 0xd38ffffff8000003 0xf4e3fffffe000000

def z751 : W := mkw 0x0185848104828000 0x006161204120a000 0xfb87c701c7c3c001 0x7ee1f1c071f0f000

def z752 : W := mkw 0x8000484e18015556 0xa000121386005555 0x0808f8fe3807ffff 0x42023e3f8e01ffff

def z753 : W := mkw 0x8527f84efc93fd56 0xe149fe13bf24ff55 0x0007f807f803fc01 0x0001fe01fe00ff00

def z754 : W := mkw 0x0184c4c500808000 0x0061313140202000 0xdb87c7c7c1c0c003 0x76e1f1f1f0703000

def z755 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0x938707ffffc003fe 0x24e1c1fffff000ff

def z756 : W := mkw 0x11b6fefdb0000000 0x046dbfbf6c000000 0x0007ff07f8000001 0x0001ffc1fe000000

def z757 : W := mkw 0x0985c5c74ec3d3d3 0x82617171d3b0f4f4 0xfb87e7c7ffc3f3c3 0x7ee1f9f1fff0fcf0

def z758 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe47f27fffe3b3333 0xf91fc9ffff8ecccc

def z759 : W := mkw 0x0194c6e5a0000000 0x006531b968000000 0xd387c7e7f8000003 0x74e1f1f9fe000000

def z760 : W := mkw 0x1136fa6db0000000 0x044dbe9b6c000000 0xc07ffffff8000003 0xf01ffffffe000000

def z761 : W := mkw 0x027a2220a0000000 0x009e888828000000 0xd3ff2727f8000003 0xf4ffc9c9fe000000

def z762 : W := mkw 0x0c332322eedbb3b1 0xc30cc8c8bbb6ecec 0xe4772727fffb3333 0xb91dc9c9fffecccc

def z763 : W := mkw 0x0105810046828200 0x0041604011a0a080 0xfb87c701c7c3c001 0x7ee1f1c071f0f000

def z764 : W := mkw 0x0985858346c38381 0x02616160d1b0e0e0 0xfb8707c7c7c303c3 0x7ee1c1f1f1f0c0f0

def z765 : W := mkw 0x1126f94db36c02a8 0x0449be536cdb00aa 0x2c07f807fffc03fd 0x0b01fe01ffff00ff

def z766 : W := mkw 0x8c0101024edbf7f7 0xe300404093b6fdfd 0x2c00000007fffffc 0x0b00000001ffffff

def z767 : W := mkw 0x93feb6b3a8015556 0xa4ffadacea005555 0xbff70701c007fffc 0x2ffdc1c07001ffff

def z768 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfffff82007ffff33 0xfffffe0801ffffcc

def z769 : W := mkw 0x8c332322eedbf7f7 0xe30cc8c8bbb6fdfd 0xec772727ffffffff 0xbb1dc9c9ffffffff

def z770 : W := mkw 0x13fefefdb1240000 0x04ffbfbf6c490000 0xd7fffffff83c0003 0xf5fffffffe0f0000

def z771 : W := mkw 0x027a2230a12c0028 0x009e888c284b000a 0xc47f273ff83c003f 0xb11fc9cffe0f000f

def z772 : W := mkw 0x82d84ffe1b6d57fe 0xa0b613ff86db55ff 0x93f0ff063ffbfc01 0x24fc3fc18ffeff00

def z773 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd3f727fff8000003 0xb4fdc9fffe000000

def z774 : W := mkw 0x13fefefdb1a48800 0x04ffbfbf6c692200 0xd3fffffff9c00003 0xf4fffffffe700000

def z775 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xd3fff80007fbfc01 0xf4fffe0001feff00

def z776 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xec7f2727fe3f3333 0xfb1fc9c9ff8fcccc

def z777 : W := mkw 0x0db6e6e5a8d8f0f3 0xc36db9b96a363c3c 0x1ff0e0e039f8f0f0 0xc7fc38380e7e3c3c

def z778 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfbf7f80007fbfc01 0x7efdfe0001feff00

def z779 : W := mkw 0x0985858346c38381 0x02616160d1b0e0e0 0x93870707c7c00302 0x24e1c1c1f1f000c0

def z780 : W := mkw 0x0985c5c546c2c2c3 0x0261717151b0b0b0 0xfb87c7c1c7c0c3c2 0x7ee1f1f071f030f0

def z781 : W := mkw 0x8248484e19255556 0xa092121386495555 0xfff8f8063ffffc01 0xfffe3e018fffff00

def z782 : W := mkw 0x03dccefd10000000 0x00f733bf44000000 0xd3fffffff8000003 0xf4fffffffe000000

def z783 : W := mkw 0x0d85c5c74edbf3f3 0xc3617171d3b6fcfc 0x3f80c0c007fbf3f0 0x4fe0303001fefcfc

def z784 : W := mkw 0x0b6fb00145b6a801 0x02dbec00516daa00 0xfffff801c7fffc01 0xfffffe0071ffff00

def z785 : W := mkw 0x02c80590036c02a8 0x00b2016400db00aa 0xfff800d807fc03fc 0xfffe003601ff00ff

def z786 : W := mkw 0x00322220a0080020 0x000c888828020008 0xc4772727f8380033 0xb11dc9c9fe0e000c

def z787 : W := mkw 0x13fefefdb1342800 0x04ffbfbf6c4d0a00 0xd3fffffff8380003 0xf4fffffffe0e0000

def z788 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe0770727fe3b0333 0x381dc1c9ff8ec0cc

def z789 : W := mkw 0x1bfefefdb0c08081 0x06ffbfbf6c302020 0xd3fffffff9c00003 0xf4fffffffe700000

def z790 : W := mkw 0x0184c4c500000000 0x0061313140000000 0xd387e7e7f8000003 0xf4e1f9f9fe000000

def z791 : W := mkw 0x0136b220a0000000 0x004dac8828000000 0xc077ff27f8000003 0xb01dffc9fe000000

def z792 : W := mkw 0x8185cccf1c83d556 0xa0617333c720f555 0xff8fffffffc7ffff 0xffe3fffffff1ffff

def z793 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xffff07ffc7fc03ff 0xffffc1fff1ff00ff

def z794 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xec772727fe3f33ff 0xbb1dc9c9ff8fccff

def z795 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xff87c7c7c7c7c3ff 0x7fe1f1f1f1f1f0ff

def z796 : W := mkw 0x8985cdcf56c3c7c7 0x22617373d5b0f1f1 0xfb8fffffffc7cfcf 0xfee3fffffff1f3f3

def z797 : W := mkw 0x127a3a38b1240000 0x049e8e8e2c490000 0x04783838383c0000 0x811e0e0e0e0f0000

def z798 : W := mkw 0x137efa7db0000000 0x04dfbe9f6c000000 0xc07fff3ff8000003 0xb01fffcffe000000

def z799 : W := mkw 0x13fefefdb12c0028 0x04ffbfbf6c4b000a 0xfffffffff83c03ff 0xfffffffffe0f00ff

def z800 : W := mkw 0x10914efdb5b6a800 0x042453bf6d6daa00 0x2c0007fffffffc02 0x0b0001ffffffff00

def z801 : W := mkw 0x0184c4c500000000 0x0061313140000000 0xfb87c7c7c7c00003 0x7ee1f1f1f1f00000

def z802 : W := mkw 0x0080058002400280 0x00200160009000a0 0xfb8707c7c7c003c3 0x7ee1c1f1f1f000f0

def z803 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0x9387c7c7c7c3c3c3 0x24e1f1f1f1f0f0f0

def z804 : W := mkw 0x06eb2492ed773198 0xc1bac924bb5dcc66 0x1b8f20dff9c730cd 0x46e3c837fe71cc33

def z805 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xbb870701c7c003c0 0x2ee1c1c071f000f0

def z806 : W := mkw 0x9127f84fbc93fd56 0xa449fe13ef24ff55 0x0007f807f803fc01 0x0001fe01fe00ff00

def z807 : W := mkw 0x0081058246430380 0x002041609190c0e0 0xf3870707c7c30303 0x3ce1c1c1f1f0c0c0

def z808 : W := mkw 0x0984c5c742c1c3c3 0x02613171d0b070f0 0xdb87c7c7c1c0c3c3 0x76e1f1f1f07030f0

def z809 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff827f807ff33ff 0xfffe09fe01ffccff

def z810 : W := mkw 0x0081058046420280 0x00204160119080a0 0x93870701c7c00000 0x24e1c1c071f00000

def z811 : W := mkw 0x0185c5c746430380 0x00617171d190c0e0 0xfb87c7c7c7c303c3 0x7ee1f1f1f1f0c0f0

def z812 : W := mkw 0x127a3a38b13c2828 0x049e8e8e2c4f0a0a 0x04783838383c3c3c 0x811e0e0e0e0f0f0f

def z813 : W := mkw 0x8bccccdd11e4c4cf 0x22f3333744793133 0x1b88d8d801c4cccc 0x46e2363600713333

def z814 : W := mkw 0x89858d895ec29695 0xa261636257b0a5a5 0x978f3f39ffc43c3c 0xa5e3cfce7ff10f0f

def z815 : W := mkw 0x93ccdcdd116444ce 0x24f3373744591133 0x1b88d8d801c4cccc 0x46e2363600713333

def z816 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0x3ff800f807fc03fc 0xcffe003e01ff00ff

def z817 : W := mkw 0x040101024f3f3330 0xc100404093cfcccc 0x2c00000007ff3330 0x0b00000001ffcccc

def z818 : W := mkw 0x13fefefdb1240000 0x04ffbfbf6c490000 0xfffffffffffc03ff 0xffffffffffff00ff

def z819 : W := mkw 0x040101024fbfbb30 0xc100404093efeecc 0x2400000007fb3330 0x0900000001fecccc

def z820 : W := mkw 0x027a2220a1240000 0x009e888828490000 0xffff2727fffc0003 0xffffc9c9ffff0000

def z821 : W := mkw 0x840101024e1b3734 0xe10040409386cdcd 0x24000000063f3f3c 0x09000000018fcfcf

def z822 : W := mkw 0x13ccdcdd11e48888 0x04f3373744792222 0x1b88d8d801c4cccc 0x46e2363600713333

def z823 : W := mkw 0x0184c5c502400280 0x00613171409000a0 0xd387c7c7c7c00003 0x74e1f1f1f1f00000

def z824 : W := mkw 0x13dcdefdb0000000 0x04f737bf6c000000 0xd38fdffff8000003 0x74e3f7fffe000000

def z825 : W := mkw 0x002321024e133310 0x8008c8409384ccc4 0xe4772727fe3b3333 0xb91dc9c9ff8ecccc

def z826 : W := mkw 0x027a2230a12c0028 0x009e888c284b000a 0x04782038383c003c 0x811e080e0e0f000f

def z827 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd3f7c7fff8000003 0x74fdf1fffe000000

def z828 : W := mkw 0x10b226b1a0000000 0x042c89ac68000000 0xc0772727f8000003 0xb01dc9c9fe000000

def z829 : W := mkw 0x026a300001342800 0x009a8c00004d0a00 0xfff8f80007fffc01 0xfffe3e0001ffff00

def z830 : W := mkw 0x034d800005a68000 0x00d360000169a000 0xfffff80007fffc01 0xfffffe0001ffff00

def z831 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0x1b87c7c7c1c3c3c3 0x46e1f1f1f070f0f0

def z832 : W := mkw 0x0985c5c74ec3d3d3 0x82617171d3b0f4f4 0xff87c7c7c7c3f3f3 0x7fe1f1f1f1f0fcfc

def z833 : W := mkw 0x8985c5c74ec3d7d7 0xa2617171d3b0f5f5 0xff87e7e7ffc7ffff 0xffe1f9f9fff1ffff

def z834 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xd38707c1c7c00002 0x74e1c1f071f00000

def z835 : W := mkw 0x00332320a61a2220 0x000cc8c829868888 0xe4772727fe3b3333 0xb91dc9c9ff8ecccc

def z836 : W := mkw 0x00322322aa091330 0x800c88c8aa8244cc 0xe4772727fe3b3333 0xb91dc9c9ff8ecccc

def z837 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xff8fff01c7c7fc01 0xffe3ffc071f1ff00

def z838 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xffffff07c7fffc03 0xffffffc1f1ffff00

def z839 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xff8fc7ffffc7c3ff 0xffe3f1fffff1f0ff

def z840 : W := mkw 0x00322220a0000000 0x000c888828000000 0x80772707f8000001 0x201dc9c1fe000000

def z841 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd7fffffff8043c03 0xf5fffffffe010f00

def z842 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xff87ffe7ffc3fff3 0xffe1fff9fff0fffc

def z843 : W := mkw 0x04322320aa183230 0xc10c88c82a860c8c 0xe4772727fe383333 0xb91dc9c9ff8e0ccc

def z844 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x64002000063b3331 0x99000800018ecccc

def z845 : W := mkw 0x880101024ec3d7d7 0xa200404093b0f5f5 0x2800000007c3c3fc 0x0a00000001f0f0ff

def z846 : W := mkw 0x040101024e9bb330 0xc100404093a6eccc 0x2c00000007fbf330 0x0b00000001fefccc

def z847 : W := mkw 0x0985c5c546c28281 0x0261717151b0a0a0 0xfb87c7c7c7c3c003 0x7ee1f1f1f1f0f000

def z848 : W := mkw 0x13ccdcdd11240000 0x04f3373744490000 0x1b88d8d801c40000 0x46e2363600710000

def z849 : W := mkw 0x0000484c10000000 0x0000121304000000 0x6c08f8fe3807ffff 0xdb023e3f8e01ffff

def z850 : W := mkw 0x0184cccd10000000 0x0061333344000000 0xd387ffc7f8000003 0x74e1fff1fe000000

def z851 : W := mkw 0x13fefefdb0004042 0x04ffbfbf6c001010 0xdbfffffff800c0c3 0xf6fffffffe003030

def z852 : W := mkw 0x13ccdcdd10000000 0x04f3373744000000 0xd38ffffff8000003 0xf4e3fffffe000000

def z853 : W := mkw 0x867a7a6eb93d7d76 0xe19e9e9bae4f5f5d 0x6c78f8fe383fffff 0xdb1e3e3f8e0fffff

def z854 : W := mkw 0x9bfefefdb0c0c4c7 0x26ffbfbf6c303131 0xdbfffffff9c4cccf 0xf6fffffffe713333

def z855 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0x9b87c701c7c0c000 0x66e1f1c071f03000

def z856 : W := mkw 0x927a7a7eb9357d56 0xa49e9e9fae4d5f55 0x6c78f8fe383fffff 0xdb1e3e3f8e0fffff

def z857 : W := mkw 0x8985c5c74ec3d7d7 0xa2617171d3b0f5f5 0xfb87c7c7c7c3c3ff 0x7ee1f1f1f1f0f0ff

def z858 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd3f7ffc7f8000003 0x74fdfff1fe000000

def z859 : W := mkw 0x8000484e18015556 0xa000121386005555 0xec78f8fe3e3fffff 0xfb1e3e3f8f8fffff

def z860 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xfbfffffff80003c3 0xfefffffffe0000f0

def z861 : W := mkw 0x13fefefdb12c0028 0x04ffbfbf6c4b000a 0xfffffffffffc003f 0xffffffffffff000f

def z862 : W := mkw 0x0985c5c546c28281 0x0261717151b0a0a0 0x9387c7c1c7c00000 0x64e1f1f071f00000

def z863 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0xe4700000063b3330 0xb91c0000018ecccc

def z864 : W := mkw 0x840101024fbfff76 0xe100404093efffdd 0x2c00000007fffffc 0x0b00000001ffffff

def z865 : W := mkw 0x127a3230a12c0028 0x049e8c8c284b000a 0x0070000000380000 0x001c0000000e0000

def z866 : W := mkw 0x0aea75c743756bc3 0x02ba9d71d0dd5af0 0x04783fc7c03c3fc2 0x811e0ff1f00f0ff0

def z867 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb8fffc7c7c3c3c3 0xfee3fff1f1f0f0f0

def z868 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x007ffffff8000003 0x801ffffffe000000

def z869 : W := mkw 0x11b6eefdb0000000 0x046dbbbf6c000000 0xd3f7e7fff8000003 0xf4fdf9fffe000000

def z870 : W := mkw 0x00100220a0000000 0x0004008828000000 0xc0070727f8000003 0x3001c1c9fe000000

def z871 : W := mkw 0x098585834ec39391 0x82616160d3b0e4e4 0xf7872727ffc33333 0xbde1c9c9fff0cccc

def z872 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xbff007f807fc03fe 0x2ffc01fe01ff00ff

def z873 : W := mkw 0x13fefefdb1342800 0x04ffbfbf6c4d0a00 0xfffffffffffc3c03 0xffffffffffff0f00

def z874 : W := mkw 0x800101024e035756 0xa00040409380d5d5 0x2c0000000607fffc 0x0b0000000181ffff

def z875 : W := mkw 0x0d85c5c746dbe3e3 0x43617171d1b6f8f8 0xfb87c7c7c7fbc3c3 0x7ee1f1f1f1fef0f0

def z876 : W := mkw 0x13fefefdb1a48800 0x04ffbfbf6c692200 0xfffffffffffccc03 0xffffffffffff3300

def z877 : W := mkw 0x13fefefdb12c0028 0x04ffbfbf6c4b000a 0xd3fffffff8380003 0xf4fffffffe0e0000

def z878 : W := mkw 0x00b226a0a0000000 0x002c89a828000000 0xd3f727e7f8000003 0xf4fdc9f9fe000000

def z879 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xbff807d807fc03fc 0x6ffe01f601ff00ff

def z880 : W := mkw 0x84336b6cf61a6666 0x610cdadb3d869999 0x887fdfd9c63ccccc 0x621ff7f6718f3333

def z881 : W := mkw 0x0127a0000492a000 0x0049e8000124a800 0xfffff80007fffc01 0xfffffe0001ffff00

def z882 : W := mkw 0x880101024ff7ffd7 0xa200404093fdfff5 0x2c00000007fffffc 0x0b00000001ffffff

def z883 : W := mkw 0x0184858102400280 0x00612160409000a0 0x93870701c7c00000 0x24e1c1c071f00000

def z884 : W := mkw 0x8985c5c74ec3d7d7 0xa2617171d3b0f5f5 0xff8fffc7c7c7ffff 0xffe3fff1f1f1ffff

def z885 : W := mkw 0x0d85858146daa2a1 0x4361616051b6a8a8 0x93870701c7f80000 0x24e1c1c071fe0000

def z886 : W := mkw 0x13eefcddb0000000 0x04fbbf376c000000 0xd38fffdff8000003 0x74e3fff7fe000000

def z887 : W := mkw 0x840101024e1b7776 0xe10040409386dddd 0x24000000063b33fc 0x09000000018eccff

def z888 : W := mkw 0x93fefefdb0000404 0x24ffbfbf6c000101 0xd3fffffff8040c0f 0xf4fffffffe010303

def z889 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe4772707fe3b3001 0xb91dc9c1ff8ecc00

def z890 : W := mkw 0x11a6fccdb0000000 0x0469bf336c000000 0x9387ff07f8000001 0x24e1ffc1fe000000

def z891 : W := mkw 0x10b26efdb0000000 0x042c9bbf6c000000 0x000727fff8000003 0x0001c9fffe000000

def z892 : W := mkw 0x00326a6cb0000000 0x000c9a9b2c000000 0xc077ff27f8000003 0xb01dffc9fe000000

def z893 : W := mkw 0x00332220a4122000 0x000cc88829048800 0xc0772727fe380003 0xb01dc9c9ff8e0000

def z894 : W := mkw 0x01b7b7b006daaaa8 0x006dedec01b6aaaa 0x0007fff80003ffff 0x0001fffe0000ffff

def z895 : W := mkw 0x0984c4c500c0c0c3 0x0261313140303030 0x9b87c7c1c1c0c0c0 0x66e1f1f070703030

def z896 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff8c7f807ffc3ff 0xfffe31fe01fff0ff

def z897 : W := mkw 0x00322a28b0000000 0x000c8a8a2c000000 0xc07f3f3ff8000003 0xb01fcfcffe000000

def z898 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0072727f8000003 0xb001c9c9fe000000

def z899 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xd3870707c7c00003 0x34e1c1c1f1f00000

def z900 : W := mkw 0x0c0101024ffff3fb 0xc300404093fffcfe 0x2c00000007fff3fc 0x0b00000001fffcff

def z901 : W := mkw 0x1bfefefdb080c043 0x06ffbfbf6c203010 0xd3fffffff800c003 0xf4fffffffe003000

def z902 : W := mkw 0x13feb6b1a0000000 0x04ffadac68000000 0xd3ff27fff8000003 0xf4ffc9fffe000000

def z903 : W := mkw 0x1985cddf56c3c3c3 0x06617377d5b0f0f0 0xfb87c7dfc7c3c3c3 0x7ee1f1f7f1f0f0f0

def z904 : W := mkw 0x12fa7efdb0000000 0x04be9fbf6c000000 0xc07f3ffff8000003 0xb01fcffffe000000

def z905 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xd387c7c7c7c003c3 0x74e1f1f1f1f000f0

def z906 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfffff8c007ffffc3 0xfffffe3001fffff0

def z907 : W := mkw 0x13fefefdb1b4a800 0x04ffbfbf6c6d2a00 0xdffffffff9fcfc03 0xf7fffffffe7f3f00

def z908 : W := mkw 0x0985c5c546c2c2c3 0x0261717151b0b0b0 0xdb87c7c7c7c0c0c3 0x76e1f1f1f1f03030

def z909 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x93ffffdff8000001 0x64fffff7fe000000

def z910 : W := mkw 0x04332222ec1b3130 0xc10cc888bb06cc4c 0xc4772727f83b3033 0xb11dc9c9fe0ecc0c

def z911 : W := mkw 0x04332320e61a2220 0x410cc8c839868888 0x80770727fe380002 0x201dc1c9ff8e0000

def z912 : W := mkw 0x04110322ee0b1330 0xc10440c8bb82c4cc 0xe4770727fe3b0333 0xb91dc1c9ff8ec0cc

def z913 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0x938707c1c7c003c2 0x24e1c1f071f000f0

def z914 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff807f807fffffe 0xfffe01fe01ffffff

def z915 : W := mkw 0x010581024e839310 0x8041604093a0e4c4 0xff8fff27ffc7ff33 0xffe3ffc9fff1ffcc

def z916 : W := mkw 0x8c904feffa4957f7 0xe32413fbfe9255fd 0x000007fff80003fe 0x000001fffe0000ff

def z917 : W := mkw 0x8d85c5c74edbf7f7 0xe3617171d3b6fdfd 0xff87c7c7c7ffffff 0x7fe1f1f1f1ffffff

def z918 : W := mkw 0x0d85c5c74edbf3f3 0xc3617171d3b6fcfc 0xff87e7e7fffbf3f3 0xffe1f9f9fffefcfc

def z919 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xfb8fffffffc3c3ff 0xfee3fffffff0f0ff

def z920 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd3ffff07f8000001 0xf4ffffc1fe000000

def z921 : W := mkw 0x880101024fefd7ff 0xa200404093fbf5ff 0x2c00000007fffffc 0x0b00000001ffffff

def z922 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xa4772707fe3b3331 0x291dc9c1ff8ecccc

def z923 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0x3f88d8d807c7fffc 0x4fe2363601f1ffff

def z924 : W := mkw 0x009007a0024802a0 0x002401e8009200a8 0xfff807f807fc03fe 0xfffe01fe01ff00ff

def z925 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xfbffffffffc00003 0xfefffffffff00000

def z926 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x84772727fe3b3031 0xa11dc9c9ff8ecc0c

def z927 : W := mkw 0x0985c5c546c28281 0x0261717151b0a0a0 0x9387c707c7c00001 0x24e1f1c1f1f00000

def z928 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe477ff27fe3bff33 0xb91dffc9ff8effcc

def z929 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb87e7e7ffc3c3c3 0xfee1f9f9fff0f0f0

def z930 : W := mkw 0x00b226b0a0000000 0x002c89ac28000000 0xc07727fff8000003 0xb01dc9fffe000000

def z931 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0x93870707c7c00000 0x24e1c1c1f1f00000

def z932 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xff87c7ffffc7ffff 0x7fe1f1fffff1ffff

def z933 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xbb8707c7c7c3c3c2 0x2ee1c1f1f1f0f0f0

def z934 : W := mkw 0x0081058046420280 0x00204160119080a0 0xfb8707c1c7c003c2 0x7ee1c1f071f000f0

def z935 : W := mkw 0x034c900001a48800 0x00d3240000692200 0xfff8f80007fffc01 0xfffe3e0001ffff00

def z936 : W := mkw 0x1136fa6db0000000 0x044dbe9b6c000000 0x0007ff27f8000003 0x0001ffc9fe000000

def z937 : W := mkw 0x127a3a38b1240008 0x049e8e8e2c490002 0x007838383804000c 0x801e0e0e0e010003

def z938 : W := mkw 0x127a3a38b1342800 0x049e8e8e2c4d0a00 0x0078383838380000 0x801e0e0e0e0e0000

def z939 : W := mkw 0x0c0101024ffffbf3 0xc300404093fffefc 0x2c00000007fffff0 0x0b00000001fffffc

def z940 : W := mkw 0x0136a220a0000000 0x004da88828000000 0xd3f7e727f8000003 0xf4fdf9c9fe000000

def z941 : W := mkw 0x13febeb9b0000000 0x04ffafae6c000000 0xd3ff3f3ff8000003 0xb4ffcfcffe000000

def z942 : W := mkw 0x127a7a7cb1342800 0x049e9e9f2c4d0a00 0x6c78f8fe383ffc03 0xdb1e3e3f8e0fff00

def z943 : W := mkw 0x040101024e0b1330 0xc10040409382c4cc 0x2000000006030330 0x080000000180c0cc

def z944 : W := mkw 0x1194cefdb0000000 0x046533bf6c000000 0x938707fff8000002 0x24e1c1fffe000000

def z945 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb8fc7ffc7c3c3c3 0xfee3f1fff1f0f0f0

def z946 : W := mkw 0x01a6e4c5a0000000 0x0069b93168000000 0xd387e7c7f8000003 0x74e1f9f1fe000000

def z947 : W := mkw 0x067a2220a93c3030 0xc19e88882a4f0c0c 0x04782020383c3030 0x811e08080e0f0c0c

def z948 : W := mkw 0x8bccdccd11e4ccc7 0x22f3373344793331 0x1b88d8d801c4cccc 0x46e2363600713333

def z949 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0x9b87c7c7c7c3c0c1 0x66e1f1f1f1f0f030

def z950 : W := mkw 0x880101024ec3d7d7 0xa200404093b0f5f5 0x2800000007c3ffc0 0x0a00000001f0fff0

def z951 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xec7ffffffe3fffff 0xfb1fffffff8fffff

def z952 : W := mkw 0x034d900005b6a800 0x00d36400016daa00 0xfff8d80007fffc00 0xfffe360001ffff00

def z953 : W := mkw 0x127a7a7cb0000000 0x049e9e9f2c000000 0xc07ffffff8000003 0xf01ffffffe000000

def z954 : W := mkw 0x0001010246030300 0x000040409180c0c0 0xfb870707c7c30303 0x7ee1c1c1f1f0c0c0

def z955 : W := mkw 0x0985c5c746d3e3c3 0x02617171d1b4f8f0 0xff87c7c7c7fbf3c3 0x7fe1f1f1f1fefcf0

def z956 : W := mkw 0x8927f84f5c93fd57 0xa249fe13d724ff55 0x0007f807f803fc01 0x0001fe01fe00ff00

def z957 : W := mkw 0x8985c5c74ec3d7d7 0xa2617171d3b0f5f5 0xfb87c7c7c7c3ffc3 0x7ee1f1f1f1f0fff0

def z958 : W := mkw 0x11b6fefdb0000000 0x046dbfbf6c000000 0x000707fff8000002 0x0001c1fffe000000

def z959 : W := mkw 0x13ccdcdd11240008 0x04f3373744490002 0x1388d8d80004000c 0x44e2363600010003

def z960 : W := mkw 0x13fefefdb0808000 0x04ffbfbf6c202000 0xdbfffffff9c0c003 0xf6fffffffe703000

def z961 : W := mkw 0x0c0101024ed3f3d3 0xc300404093b4fcf4 0x2800000007c3f3c0 0x0a00000001f0fcf0

def z962 : W := mkw 0x00322220a0000000 0x000c888828000000 0xe4772727fe380003 0xb91dc9c9ff8e0000

def z963 : W := mkw 0x0b5dc27745afc16b 0x02d7709dd16bf05a 0x047fc03fc03fc03d 0x811ff00ff00ff00f

def z964 : W := mkw 0x0985858146c2c2c3 0x0261616051b0b0b0 0x9b870701c7c0c0c0 0x26e1c1c071f03030

def z965 : W := mkw 0x00322220a0000000 0x000c888828000000 0x00072727f8000003 0x0001c9c9fe000000

def z966 : W := mkw 0x0185c5c746838300 0x00617171d1a0e0c0 0xfb87c7c7c7c3c303 0x7ee1f1f1f1f0f0c0

def z967 : W := mkw 0x127a3a38b1240800 0x049e8e8e2c490200 0x0078383838040c00 0x801e0e0e0e010300

def z968 : W := mkw 0x04332322ee9bb330 0xc10cc8c8bba6eccc 0xec772727fffbf333 0xbb1dc9c9fffefccc

def z969 : W := mkw 0x03feb6b0a0000000 0x00ffadac28000000 0xd3fffffff8000003 0xf4fffffffe000000

def z970 : W := mkw 0x0985c5c546c2c2c3 0x0261717151b0b0b0 0x938707c1c7c000c0 0x24e1c1f071f00030

def z971 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xff8fdfdfc7c7ffff 0x7fe3f7f7f1f1ffff

def z972 : W := mkw 0x11b6fefdb0000000 0x046dbfbf6c000000 0x400ffffff8000003 0xd003fffffe000000

def z973 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xff87e7c7c7c3f3c3 0xffe1f9f1f1f0fcf0

def z974 : W := mkw 0x13fefefdb1342800 0x04ffbfbf6c4d0a00 0xfffffffff83ffc03 0xfffffffffe0fff00

def z975 : W := mkw 0x0184cdcd12400280 0x00613373449000a0 0xff8fffffffc403ff 0xffe3fffffff100ff

def z976 : W := mkw 0x0985c5c746cbc3e3 0x02617171d1b2f0f8 0xff87c7c7c7fbc3f3 0x7fe1f1f1f1fef0fc

def z977 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x84772727fe383332 0xa11dc9c9ff8e0ccc

def z978 : W := mkw 0x13fefefdb1240000 0x04ffbfbf6c490000 0xd3fffffffff80003 0xf4fffffffffe0000

def z979 : W := mkw 0x0127b0000492a800 0x0049ec000124aa00 0x6c0ff8f80007ffff 0xdb03fe3e0001ffff

def z980 : W := mkw 0x0905c1474683c343 0x02417051d1a0f0d0 0xfb87c707c7c3c303 0x7ee1f1c1f1f0f0c0

def z981 : W := mkw 0x13fefefdb0102000 0x04ffbfbf6c040800 0xd7fffffff8383003 0xf5fffffffe0e0c00

def z982 : W := mkw 0x02580230012c0028 0x0096008c004b000a 0xfff800f807fc03fe 0xfffe003e01ff00ff

def z983 : W := mkw 0x04232102ee133310 0xc108c840bb84ccc4 0xe4772707fe3b3303 0xb91dc9c1ff8eccc0

def z984 : W := mkw 0x137eba38b0000000 0x04dfae8e2c000000 0xd3ffff3ff8000003 0xf4ffffcffe000000

def z985 : W := mkw 0x0c0101024ecbd3f3 0xc300404093b2f4fc 0x2800000007c3c3f0 0x0a00000001f0f0fc

def z986 : W := mkw 0x042321024e1b3330 0xc108c8409386cccc 0x24702000063b3330 0x891c0800018ecccc

def z987 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x93f70707f8000000 0x24fdc1c1fe000000

def z988 : W := mkw 0x0105800004828000 0x004160000120a000 0xfb87c707c7c3c003 0x7ee1f1c1f1f0f000

def z989 : W := mkw 0x0185c4c70483c142 0x00617131c120f050 0xfb87c7c7c7c3c3c3 0x7ee1f1f1f1f0f0f0

def z990 : W := mkw 0x11a6fccdb0000000 0x0469bf336c000000 0xd38ffffff8000003 0xf4e3fffffe000000

def z991 : W := mkw 0x04322322ea091330 0xc10c88c8ba8244cc 0xe4772727fe380333 0xb91dc9c9ff8e00cc

def z992 : W := mkw 0x10b26efdb0000000 0x042c9bbf6c000000 0xc07ffffff8000003 0xf01ffffffe000000

def z993 : W := mkw 0x0ad807b1436c02a9 0x02b601ec50db00aa 0xfff807f9c7fc03fe 0xfffe01fe71ff00ff

def z994 : W := mkw 0x0184858102400280 0x00612160409000a0 0xfb8707c1c7c003c2 0x7ee1c1f071f000f0

def z995 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xfb87ffffffc3ffff 0x7ee1fffffff0ffff

def z996 : W := mkw 0x12fa3eb8b0000000 0x04be8fae2c000000 0xd3ff3ffff8000003 0xf4ffcffffe000000

def z997 : W := mkw 0x127a7a7cb12c0028 0x049e9e9f2c4b000a 0x6c78f8fe383c03ff 0xdb1e3e3f8e0f00ff

def z998 : W := mkw 0x927a3a38b9343c14 0xa49e8e8e2e4d0f05 0x04783838383c3c3c 0x811e0e0e0e0f0f0f

def z999 : W := mkw 0x1184cccdb0000000 0x046133336c000000 0xd387c7c7f8000003 0x74e1f1f1fe000000

def z1000 : W := mkw 0x0105c1464683c342 0x0041705191a0f0d0 0xfb87c7c7c7c3c3c3 0x7ee1f1f1f1f0f0f0

def z1001 : W := mkw 0x8000484e18015556 0xa000121386005555 0xff88f8fe3fc7ffff 0xffe23e3f8ff1ffff

def z1002 : W := mkw 0x067a3220a13c2820 0x419e8c88284f0a08 0x0070000000380000 0x001c0000000e0000

def z1003 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff827fe3ffc03ff 0xfffe09ff8fff00ff

def z1004 : W := mkw 0x11b6feedb0000000 0x046dbfbb6c000000 0xd3f7ffe7f8000003 0xf4fdfff9fe000000

def z1005 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb8fc7dfc7c7c3cf 0x7ee3f1f7f1f1f0f3

def z1006 : W := mkw 0x00332322e6132300 0x000cc8c8b984c8c0 0xe4772727fe3b3303 0xb91dc9c9ff8eccc0

def z1007 : W := mkw 0x02d806b001240000 0x00b601ac00490000 0xfff807f807fc03fe 0xfffe01fe01ff00ff

def z1008 : W := mkw 0x93fefefdb1a4cc46 0x24ffbfbf6c693311 0xdbfffffff9c4cccf 0xf6fffffffe713333

def z1009 : W := mkw 0x8800484f58015557 0xa2001213d6005555 0x6c08f8fff807ffff 0xdb023e3ffe01ffff

def z1010 : W := mkw 0x009007b0024802a8 0x002401ec009200aa 0x6c08fff80007ffff 0xdb023ffe0001ffff

def z1011 : W := mkw 0x840101024f7f77fe 0xe100404093dfddff 0x2c00000007fffffc 0x0b00000001ffffff

def z1012 : W := mkw 0x065903324f3f3338 0xc19640cc93cfccce 0x24780038063f333c 0x891e000e018fcccf

def z1013 : W := mkw 0x13fef6f5a0000000 0x04ffbdbd68000000 0xd3f7e7e7f8000003 0xf4fdf9f9fe000000

def z1014 : W := mkw 0x0985c5c546c28281 0x0261717151b0a0a0 0xfb87c7c7c7c003c3 0x7ee1f1f1f1f000f0

def z1015 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x6c08f800063fff31 0xdb023e00018fffcc

def z1016 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb8707c7c7c003c2 0x7ee1c1f1f1f000f0

def z1017 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xfbfffffff803c003 0xfefffffffe00f000

def z1018 : W := mkw 0x137efa6db0000000 0x04dfbe9b6c000000 0xd3ffff27f8000003 0xf4ffffc9fe000000

def z1019 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xd3f807f807f803fe 0xf4fe01fe01fe00ff

def z1020 : W := mkw 0x0185c5c506c28280 0x0061717141b0a0a0 0xfb87c7c7c7c3c3c3 0x7ee1f1f1f1f0f0f0

def z1021 : W := mkw 0x93fefefdb0004446 0x24ffbfbf6c001111 0xd3fffffff80000cf 0xf4fffffffe000033

def z1022 : W := mkw 0x02c8058003640280 0x00b2016000d900a0 0xfff807f807fc03fe 0xfffe01fe01ff00ff

def z1023 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xf7fffffffe380003 0xfdffffffff8e0000

def z1024 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfffff8263ffffc03 0xfffffe098fffff00

def z1025 : W := mkw 0x0985858346c38381 0x02616160d1b0e0e0 0xb3870701c7c30300 0x2ce1c1c071f0c0c0

def z1026 : W := mkw 0x040101024e5b33b8 0xc10040409396ccee 0x24000000063b33fc 0x09000000018eccff

def z1027 : W := mkw 0x80326a6cb0004446 0x200c9a9b2c001111 0xc87ffffff804cccf 0xf21ffffffe013333

def z1028 : W := mkw 0x0184c4c500400080 0x0061313140100020 0xdb87c7c7c1c000c3 0x76e1f1f1f0700030

def z1029 : W := mkw 0x1985ddcf56c3c3c3 0x06617773d5b0f0f0 0xfb87dfc7c7c3c3c3 0x7ee1f7f1f1f0f0f0

def z1030 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x93f7fffff8000003 0x24fdfffffe000000

def z1031 : W := mkw 0x13fefefdb1240008 0x04ffbfbf6c490002 0xd3fffffff804000f 0xf4fffffffe010003

def z1032 : W := mkw 0x02580320032c0220 0x009600c800cb0088 0xfff807f807fc03fe 0xfffe01fe01ff00ff

def z1033 : W := mkw 0x13fefefdb1e48888 0x04ffbfbf6c792222 0xdbfffffff9c4cccf 0xf6fffffffe713333

def z1034 : W := mkw 0x067a3220a93c3830 0xc19e8c882a4f0e0c 0x0470202038383030 0x811c08080e0e0c0c

def z1035 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd3f7ff27f8000003 0xb4fdffc9fe000000

def z1036 : W := mkw 0x02fa26b0a0000000 0x00be89ac28000000 0xd3f72727f8000003 0xb4fdc9c9fe000000

def z1037 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe47fff27fe3b3333 0xf91fffc9ff8ecccc

def z1038 : W := mkw 0x0985c5c74ec3d3d3 0x82617171d3b0f4f4 0xff8fe7ffffc7f3ff 0xffe3f9fffff1fcff

def z1039 : W := mkw 0x00222000a0000000 0x0008880028000000 0xc0072707f8000003 0x3001c9c1fe000000

def z1040 : W := mkw 0x88904fff5a4957ff 0xa22413ffd69255ff 0x000007fff80003fe 0x000001fffe0000ff

def z1041 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0x9b87c7c7c7c0c3c2 0x66e1f1f1f1f030f0

def z1042 : W := mkw 0x13fefefdb1640088 0x04ffbfbf6c590022 0xfffffffff9c403ff 0xfffffffffe7100ff

def z1043 : W := mkw 0x84332322ee1b3734 0xe10cc8c8bb86cdcd 0xe4772727fe3f3f3f 0xb91dc9c9ff8fcfcf

def z1044 : W := mkw 0x04333322ee1b3b30 0xc10cccc8bb86cecc 0xe4773f27fe3b3f33 0xb91dcfc9ff8ecfcc

def z1045 : W := mkw 0x0985858346c3c3c3 0x02616160d1b0f0f0 0xfb87c701c7c3c3c1 0x7ee1f1c071f0f0f0

def z1046 : W := mkw 0x10b26efdb0000000 0x042c9bbf6c000000 0x807707fff8000002 0x201dc1fffe000000

def z1047 : W := mkw 0x8184cdcf1a4157d6 0xa0613373c69055f5 0xff8fffffffc7ffff 0xffe3fffffff1ffff

def z1048 : W := mkw 0x04332322ee5b33b8 0xc10cc8c8bb96ccee 0xe4772727fe3b33ff 0xb91dc9c9ff8eccff

def z1049 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xf3870701c7c30001 0x3ce1c1c071f0c000

def z1050 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xec7727e7fe3b33f3 0xfb1dc9f9ff8eccfc

def z1051 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xf387c707c7c3c303 0x3ce1f1c1f1f0f0c0

def z1052 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfffff83807fffc3d 0xfffffe0e01ffff0f

def z1053 : W := mkw 0x8401494e5e1b7776 0xe10052539786dddd 0x2c08d8d8063ffffc 0x4b023636018fffff

def z1054 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0x9387ff07ffc3fc01 0x24e1ffc1fff0ff00

def z1055 : W := mkw 0x127a3230a0000000 0x049e8c8c28000000 0xc0772727f8000003 0xb01dc9c9fe000000

def z1056 : W := mkw 0x12fa6efdb0000000 0x04be9bbf6c000000 0xd3ff27fff8000003 0xf4ffc9fffe000000

def z1057 : W := mkw 0x927a7a7eb92d557e 0xa49e9e9fae4b555f 0x6c78f8fe383fffff 0xdb1e3e3f8e0fffff

def z1058 : W := mkw 0x0127b0000492a800 0x0049ec000124aa00 0xfff7f80007fbfc01 0xfffdfe0001feff00

def z1059 : W := mkw 0x8985cdcf56c3c7c7 0x22617373d5b0f1f1 0xff8fdfffc7c7cfff 0xffe3f7fff1f1f3ff

def z1060 : W := mkw 0x127a3230a12c0028 0x049e8c8c284b000a 0x04780038003c003c 0x811e000e000f000f

def z1061 : W := mkw 0x127a3230a1342800 0x049e8c8c284d0a00 0x0070000000380000 0x001c0000000e0000

def z1062 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xfffffffff807ffff 0xfffffffffe01ffff

def z1063 : W := mkw 0x036eb00001240000 0x00dbac0000490000 0xfffff80007fffc01 0xfffffe0001ffff00

def z1064 : W := mkw 0x02fa6efcb0000000 0x00be9bbf2c000000 0xd3fffffff8000003 0xf4fffffffe000000

def z1065 : W := mkw 0x13fefefdb1240800 0x04ffbfbf6c490200 0xd3fffffff8040c03 0xf4fffffffe010300

def z1066 : W := mkw 0x00332222ac133110 0x800cc888ab04cc44 0xe4772727fe3b3333 0xb91dc9c9ff8ecccc

def z1067 : W := mkw 0x867a3a28b93c3c34 0xe19e8e8a2e4f0f0d 0x04783838383c3c3c 0x811e0e0e0e0f0f0f

def z1068 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x0000000000033330 0x000000000000cccc

def z1069 : W := mkw 0x167a3a38b93c3038 0xc59e8e8e2e4f0c0e 0x04783838383c303c 0x811e0e0e0e0f0c0f

def z1070 : W := mkw 0x02c8049001640088 0x00b2012400590022 0xfff800f807fc03fe 0xfffe003e01ff00ff

def z1071 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xff8fc7c7c7c7c3c3 0xffe3f1f1f1f1f0f0

def z1072 : W := mkw 0x06d807b0e36c02a8 0x41b601ec38db00aa 0xfff807f9c7fc03fe 0xfffe01fe71ff00ff

def z1073 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x0000000006380330 0x00000000018e00cc

def z1074 : W := mkw 0x0984c5c502c0c2c3 0x0261317140b030b0 0xfb87c7c7c7c0c3c3 0x7ee1f1f1f1f030f0

def z1075 : W := mkw 0x0000484c10000000 0x0000121304000000 0xc00ffffff8000003 0xf003fffffe000000

def z1076 : W := mkw 0x13fefefdb0080020 0x04ffbfbf6c020008 0xd7fffffff8380033 0xf5fffffffe0e000c

def z1077 : W := mkw 0x0984c5c7424143c3 0x02613171d09050f0 0xfb87c7c7c7c003c3 0x7ee1f1f1f1f000f0

def z1078 : W := mkw 0x00b266e5a0000000 0x002c99b968000000 0xc07727e7f8000003 0xb01dc9f9fe000000

def z1079 : W := mkw 0x0c0101024e5b73f3 0xc30040409396dcfc 0x24000000063b33f0 0x09000000018eccfc

def z1080 : W := mkw 0x8d27e84ffc93f557 0xe349fa13ff24fd55 0x0007f807f803fc01 0x0001fe01fe00ff00

def z1081 : W := mkw 0x040101024fffbbb8 0xc100404093ffeeee 0x2c00000007fffffc 0x0b00000001ffffff

def z1082 : W := mkw 0x8000484e18015556 0xa000121386005555 0xec0ffffff807ffff 0xfb03fffffe01ffff

def z1083 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xbfffd80007fffc00 0x6ffff60001ffff00

def z1084 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xfb8fffffffc3ffc3 0xfee3fffffff0fff0

def z1085 : W := mkw 0x0985cdcf56c3c3c3 0x02617373d5b0f0f0 0xfb87c7ffffc3c3c3 0x7ee1f1fffff0f0f0

def z1086 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x24700000063b3330 0x091c0000018ecccc

def z1087 : W := mkw 0x064901024f3f3330 0xc192404093cfcccc 0xfff8000007ff3330 0xfffe000001ffcccc

def z1088 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x93ffff3ff8000001 0xa4ffffcffe000000

def z1089 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff8fff807fc03ff 0xfffe3ffe01ff00ff

def z1090 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x2c000000063fff30 0x0b000000018fffcc

def z1091 : W := mkw 0x127a3230a1342800 0x049e8c8c284d0a00 0x04783800003c3c00 0x811e0e00000f0f00

def z1092 : W := mkw 0x8000080818001414 0xa000020206000505 0x6c08f8f83807ffff 0xdb023e3e0e01ffff

def z1093 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xff87ffc7ffc7ffff 0x7fe1fff1fff1ffff

def z1094 : W := mkw 0x0905810246c3c3c3 0x0241604091b0f0f0 0xfb87c707c7c3c3c3 0x7ee1f1c1f1f0f0f0

def z1095 : W := mkw 0x067a2230a13c2028 0x419e888c284f080a 0x0070000000380000 0x001c0000000e0000

def z1096 : W := mkw 0x0c0101024edbb3b1 0xc300404093b6ecec 0x2400000007fb3330 0x0900000001fecccc

def z1097 : W := mkw 0x0985cdcf56c3c3c3 0x02617373d5b0f0f0 0xfb87ffc7ffc3c3c3 0x7ee1fff1fff0f0f0

def z1098 : W := mkw 0x13fefefdb1a48800 0x04ffbfbf6c692200 0xfffffffff9c7fc03 0xfffffffffe71ff00

def z1099 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe4770727fe380332 0xb91dc1c9ff8e00cc

def z1100 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff8dff807fccffe 0xfffe37fe01ff33ff

def z1101 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xc0772727fe380333 0xb01dc9c9ff8e00cc

def z1102 : W := mkw 0x0d85c5c74ed3f3d3 0xc3617171d3b4fcf4 0xfb87c7c7c7c3f3c3 0x7ee1f1f1f1f0fcf0

def z1103 : W := mkw 0x0984c4c700c1c1c3 0x02613131c0307070 0xfb87c7c7c1c3c3c3 0x7ee1f1f1f070f0f0

def z1104 : W := mkw 0x13fefefdb0400088 0x04ffbfbf6c100022 0xd3fffffff80000cf 0xf4fffffffe000033

def z1105 : W := mkw 0x93fefefdb0004446 0x24ffbfbf6c001111 0xfffffffff804cfff 0xfffffffffe0133ff

def z1106 : W := mkw 0x167a3a38b93c3830 0xc59e8e8e2e4f0e0c 0x04783838383c3c30 0x811e0e0e0e0f0f0c

def z1107 : W := mkw 0x02480100036c02a8 0x0092004000db00aa 0xfff800f807fc03fe 0xfffe003e01ff00ff

def z1108 : W := mkw 0x067a3220a13c2820 0x419e8c88284f0a08 0x04783800003c3c00 0x811e0e00000f0f00

def z1109 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x80770707fe380000 0x201dc1c1ff8e0000

def z1110 : W := mkw 0x1194cefdb0000000 0x046533bf6c000000 0x0007c7fff8000003 0x0001f1fffe000000

def z1111 : W := mkw 0x03eefccd10000000 0x00fbbf3344000000 0xd3fffffff8000003 0xf4fffffffe000000

def z1112 : W := mkw 0x13fefefdb1640088 0x04ffbfbf6c590022 0xd3fffffff9c00003 0xf4fffffffe700000

def z1113 : W := mkw 0x00332322e60b0320 0x000cc8c8b982c0c8 0xe4772727fe3b0333 0xb91dc9c9ff8ec0cc

def z1114 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfff83ff807fc3ffe 0xfffe0ffe01ff0fff

def z1115 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd3ff07fff8000002 0xf4ffc1fffe000000

def z1116 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb87ffc7c7c3ffc3 0x7ee1fff1f1f0fff0

def z1117 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0x9b8707c1c7c000c0 0x66e1c1f071f00030

def z1118 : W := mkw 0x04322322ea193330 0xc10c88c8ba864ccc 0xc4772727f8383333 0xb11dc9c9fe0e0ccc

def z1119 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xfb8fdfffffc7cfff 0x7ee3f7fffff1f3ff

def z1120 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0x3ff8f80007fffc00 0xcffe3e0001ffff00

def z1121 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0x97fff80007fffc01 0xa5fffe0001ffff00

def z1122 : W := mkw 0x0985c5c546c28281 0x0261717151b0a0a0 0x938707c7c7c00002 0x24e1c1f1f1f00000

def z1123 : W := mkw 0x11b6fefdb0000000 0x046dbfbf6c000000 0xd387fffff8000003 0x74e1fffffe000000

def z1124 : W := mkw 0x040101024e5b33b0 0xc10040409396ccec 0x2c00000007fb33f0 0x0b00000001feccfc

def z1125 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xbff7f80007fffc01 0x2ffdfe0001ffff00

def z1126 : W := mkw 0x12d807b1a36c02a8 0x04b601ec68db00aa 0xfff807f9c7fc03fe 0xfffe01fe71ff00ff

def z1127 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd3fffffff803fc03 0xf4fffffffe00ff00

def z1128 : W := mkw 0x037efa6cb0000000 0x00dfbe9b2c000000 0xd3fffffff8000003 0xf4fffffffe000000

def z1129 : W := mkw 0x0985c4c504c2c0c3 0x026171314130b030 0xfb87c7c7c7c3c0c3 0x7ee1f1f1f1f0f030

def z1130 : W := mkw 0x088145c7464343c3 0x02205171d190d0f0 0xfb8707c7c7c303c3 0x7ee1c1f1f1f0c0f0

def z1131 : W := mkw 0x0985858346c38381 0x02616160d1b0e0e0 0xfb87c707c7c3c303 0x7ee1f1c1f1f0f0c0

def z1132 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe47f273ffe3f333f 0xb91fc9cfff8fcccf

def z1133 : W := mkw 0x0136e265a0000000 0x004db89968000000 0xc077e727f8000003 0xb01df9c9fe000000

def z1134 : W := mkw 0x067a2230a93c3038 0xc19e888c2a4f0c0e 0x0470202038383030 0x811c08080e0e0c0c

def z1135 : W := mkw 0x840101024e1b7776 0xe10040409386dddd 0x24000000063bff30 0x09000000018effcc

def z1136 : W := mkw 0x10904efdb0000000 0x042413bf6c000000 0xc00707fff8000003 0x3001c1fffe000000

def z1137 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xf7f007f807f803fe 0xbdfc01fe01fe00ff

def z1138 : W := mkw 0x13ccdcdd11240800 0x04f3373744490200 0x1388d8d800040c00 0x44e2363600010300

def z1139 : W := mkw 0x93fefefdb16444ce 0x24ffbfbf6c591133 0xdbfffffff9c4cccf 0xf6fffffffe713333

def z1140 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x64000020063b3332 0x99000008018ecccc

def z1141 : W := mkw 0x04332332ee1b3338 0xc10cc8ccbb86ccce 0xe477273ffe3b333f 0xb91dc9cfff8ecccf

def z1142 : W := mkw 0x867a6a7eb93d757e 0xe19e9a9fae4f5d5f 0x6c78f8fe383fffff 0xdb1e3e3f8e0fffff

def z1143 : W := mkw 0x008105824e431390 0x802041609390c4e4 0xff8f27ffffc733ff 0xffe3c9fffff1ccff

def z1144 : W := mkw 0x8000484e18015556 0xa000121386005555 0x2c08f8f83807fffc 0xcb023e3e0e01ffff

def z1145 : W := mkw 0x0c332322ee5b73f3 0xc30cc8c8bb96dcfc 0xe4772727fe3b33f3 0xb91dc9c9ff8eccfc

def z1146 : W := mkw 0x0984848100c08081 0x0261212040302020 0x93870701c1c00000 0x24e1c1c070700000

def z1147 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe47f3f27fe3f3f33 0xb91fcfc9ff8fcfcc

def z1148 : W := mkw 0x84332322ee1b7776 0xe10cc8c8bb86dddd 0xec7fff27fe3fffff 0xfb1fffc9ff8fffff

def z1149 : W := mkw 0x0249000005b6a800 0x00924000016daa00 0xfff8f80007fffc01 0xfffe3e0001ffff00

def z1150 : W := mkw 0x13feb6b1a0000000 0x04ffadac68000000 0xd3ffff27f8000003 0xf4ffffc9fe000000

def z1151 : W := mkw 0x0985cdcd56c28281 0x0261737355b0a0a0 0xd38fffffffc00003 0xf4e3fffffff00000

def z1152 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xf3870701c7c00302 0x3ce1c1c071f000c0

def z1153 : W := mkw 0x040101024f7f33b8 0xc100404093dfccee 0x2400000007fb3330 0x0900000001fecccc

def z1154 : W := mkw 0x040101024f3f3b30 0xc100404093cfcecc 0x24000000063f3f30 0x09000000018fcfcc

def z1155 : W := mkw 0x000101024e031310 0x800040409380c4c4 0x2400000006033330 0x090000000180cccc

def z1156 : W := mkw 0x04332222ec133110 0xc10cc888bb04cc44 0xe4772727fe3b3003 0xb91dc9c9ff8ecc00

def z1157 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd7fffffff804003f 0xf5fffffffe01000f

def z1158 : W := mkw 0x13ffb7b1a7feaaa8 0x04ffedec69ffaaaa 0x93f70701c7f80000 0x24fdc1c071fe0000

def z1159 : W := mkw 0x1136b221a0000000 0x044dac8868000000 0xc0772727f8000003 0xb01dc9c9fe000000

def z1160 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x04772727f83b3333 0x811dc9c9fe0ecccc

def z1161 : W := mkw 0x8248484e19255556 0xa092121386495555 0xfff800fe3ffc03fe 0xfffe003f8fff00ff

def z1162 : W := mkw 0x036fb000a5b6a800 0x00dbec00296daa00 0xfffff807fffffc01 0xfffffe01ffffff00

def z1163 : W := mkw 0x04332320ee1a3230 0xc10cc8c83b868c8c 0xc4772727fe383033 0xb11dc9c9ff8e0c0c

def z1164 : W := mkw 0x8000484e18015556 0xa000121386005555 0x0408f8fe3807ffff 0x81023e3f8e01ffff

def z1165 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0x9387c701c7c3c001 0x24e1f1c071f0f000

def z1166 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x6c0800f8063f33fe 0xdb02003e018fccff

def z1167 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xfb87c7c7ffc3c3c3 0x7ee1f1f1fff0f0f0

def z1168 : W := mkw 0x026b200005362000 0x009ac800014d8800 0xfffff80007fffc01 0xfffffe0001ffff00

def z1169 : W := mkw 0x0985858346c3c3c3 0x02616160d1b0f0f0 0x93870701c7c3c000 0x24e1c1c071f0f000

def z1170 : W := mkw 0x80814dce5e4357d6 0xa02053739790d5f5 0xff8fffffffc7ffff 0xffe3fffffff1ffff

def z1171 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xec77e727fe3bf333 0xfb1df9c9ff8efccc

def z1172 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe0772707fe3b3303 0x381dc9c1ff8eccc0

def z1173 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xc0772727fe3b3003 0xb01dc9c9ff8ecc00

def z1174 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xbb87c7c1c7c3c3c0 0x6ee1f1f071f0f0f0

def z1175 : W := mkw 0x8984cccf18c1d5d7 0xa2613333c6307575 0xff8ffffff9c7ffff 0xffe3fffffe71ffff

def z1176 : W := mkw 0x040101024e9bbb30 0xc100404093a6eecc 0x24000000063bff30 0x09000000018effcc

def z1177 : W := mkw 0x0d85c5c74ecbd3f3 0xc3617171d3b2f4fc 0xfb87c7c7c7c3c3f3 0x7ee1f1f1f1f0f0fc

def z1178 : W := mkw 0x84332322ee1b7776 0xe10cc8c8bb86dddd 0xe4772727fe3b33ff 0xb91dc9c9ff8eccff

def z1179 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xff8fffc7ffc7ffc3 0xffe3fff1fff1fff0

def z1180 : W := mkw 0x8985cdcd56c2c6c7 0x2261737355b0b1b1 0x9b8fdfd9c7c4cccc 0x66e3f7f671f13333

def z1181 : W := mkw 0x0985cdcf56c3c3c3 0x02617373d5b0f0f0 0xff8fffffffc7ffc3 0xffe3fffffff1fff0

def z1182 : W := mkw 0x0985c4c74483c143 0x02617131d120f050 0xfb87c7c7c7c3c003 0x7ee1f1f1f1f0f000

def z1183 : W := mkw 0x13dccefdb0000000 0x04f733bf6c000000 0xd3ffc7fff8000003 0xf4fff1fffe000000

def z1184 : W := mkw 0x0c0101024e9bf373 0xc300404093a6fcdc 0x24000000063bf330 0x09000000018efccc

def z1185 : W := mkw 0x0985c5d746c3c3cb 0x02617175d1b0f0f2 0xfb87c7dfc7c3c3cf 0x7ee1f1f7f1f0f0f3

def z1186 : W := mkw 0x10322a38b0000000 0x040c8a8e2c000000 0xc077273ff8000003 0xb01dc9cffe000000

def z1187 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0xfbf007f807f803fe 0x7efc01fe01fe00ff

def z1188 : W := mkw 0x00322320a2080220 0x000c88c828820088 0xc0772727fe380003 0xb01dc9c9ff8e0000

def z1189 : W := mkw 0x8105c94e5e83d756 0xa041725397a0f5d5 0xff8fffffffc7ffff 0xffe3fffffff1ffff

def z1190 : W := mkw 0x11a6fccdb0000000 0x0469bf336c000000 0x0007ffc7f8000003 0x0001fff1fe000000

def z1191 : W := mkw 0x07ffb7b0e7feaaa8 0x41ffedec39ffaaaa 0x93f70701c7f80000 0x24fdc1c071fe0000

def z1192 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xa4770727fe3b3332 0x291dc1c9ff8ecccc

def z1193 : W := mkw 0x0185c4c504828000 0x006171314120a000 0xd387c7c7c7c00003 0x74e1f1f1f1f00000

def z1194 : W := mkw 0x036fb01005b6a808 0x00dbec04016daa02 0xfffff81807fffc0d 0xfffffe0601ffff03

def z1195 : W := mkw 0x0c332322ee9bf373 0xc30cc8c8bba6fcdc 0xe4772727fe3bf333 0xb91dc9c9ff8efccc

def z1196 : W := mkw 0x09b6e6e5a0c0c0c3 0x026db9b968303030 0xdbf7e7e7f9c0c0c3 0xf6fdf9f9fe703030

def z1197 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfffff8f807fffc03 0xfffffe3e01ffff00

def z1198 : W := mkw 0x04322222a8193130 0xc10c8888aa064c4c 0xe4772727f83b3333 0xb91dc9c9fe0ecccc

def z1199 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfff7c7c7c7fbc3c3 0xfffdf1f1f1fef0f0

def z1200 : W := mkw 0x001103224e0b1330 0x800440c89382c4cc 0xe4772727fe3b3333 0xb91dc9c9ff8ecccc

def z1201 : W := mkw 0x02d807b0a36c02a8 0x00b601ec28db00aa 0xfff807fffffc03fe 0xfffe01ffffff00ff

def z1202 : W := mkw 0x13feb6b1a0000000 0x04ffadac68000000 0x93f70727f8000002 0x24fdc1c9fe000000

def z1203 : W := mkw 0x0985c5c746c38381 0x02617171d1b0e0e0 0xf387c7c7c7c30303 0x7ce1f1f1f1f0c0c0

def z1204 : W := mkw 0x1bfefefdb1e4c0cb 0x06ffbfbf6c793032 0xdbfffffff9c4c0cf 0xf6fffffffe713033

def z1205 : W := mkw 0x1126f84db0000000 0x0449be136c000000 0xc007ff07f8000003 0x3001ffc1fe000000

def z1206 : W := mkw 0x04332320e61a2220 0x410cc8c839868888 0xe4772727fe380333 0xb91dc9c9ff8e00cc

def z1207 : W := mkw 0x080101024ec3d3d3 0x8200404093b0f4f4 0x2c00000007c3f3f0 0x0b00000001f0fcfc

def z1208 : W := mkw 0x1bccdcdd11e4c0cb 0x06f3373744793032 0x1b88d8d801c4c0cc 0x46e2363600713033

def z1209 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb8fdfc7c7c7cfc3 0x7ee3f7f1f1f1f3f0

def z1210 : W := mkw 0x0985858346c3c3c3 0x02616160d1b0f0f0 0xfb870707c7c3c3c3 0x3ee1c1c1f1f0f0f0

def z1211 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xdbfffffff804cc03 0xf6fffffffe013300

def z1212 : W := mkw 0x04332322ee5b33b0 0xc10cc8c8bb96ccec 0xec772727fffb33f3 0xbb1dc9c9fffeccfc

def z1213 : W := mkw 0x00322220a0000000 0x000c888828000000 0x80770727f8000002 0x201dc1c9fe000000

def z1214 : W := mkw 0x04332322e61b2320 0x410cc8c8b986c8c8 0xe0772727fe3b0303 0xb81dc9c9ff8ec0c0

def z1215 : W := mkw 0x8985cdcf56c3c7c7 0x22617373d5b0f1f1 0xfb87c7dfc7c3c3cf 0x7ee1f1f7f1f0f0f3

def z1216 : W := mkw 0x0985c5c74ec3d3d3 0x82617171d3b0f4f4 0xfb87c7e7ffc3c3f3 0x7ee1f1f9fff0f0fc

def z1217 : W := mkw 0x040101024e1b7372 0xc10040409386dcdc 0x2c000000063bf3f0 0x0b000000018efcfc

def z1218 : W := mkw 0x008145c6464343c2 0x002051719190d0f0 0xfb87c7c7c7c3c3c3 0x7ee1f1f1f1f0f0f0

def z1219 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xf7f7f80007fbfc01 0xbdfdfe0001feff00

def z1220 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xf7fffffff8033003 0xfdfffffffe00cc00

def z1221 : W := mkw 0x8985c5c74ec3d7d7 0xa2617171d3b0f5f5 0xff8fc7ffc7c7ffff 0xffe3f1fff1f1ffff

def z1222 : W := mkw 0x1136fa6db0000000 0x044dbe9b6c000000 0x8077ff07f8000001 0x201dffc1fe000000

def z1223 : W := mkw 0x01b6eeedb0000000 0x006dbbbb6c000000 0xd3fffffff8000003 0xf4fffffffe000000

def z1224 : W := mkw 0x1bfefefdb1e4c8c3 0x06ffbfbf6c793230 0xdbfffffff9c4ccc3 0xf6fffffffe713330

def z1225 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xd387c701c7c00001 0x74e1f1c071f00000

def z1226 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xfb87c7c1c7c3c3c3 0x7ee1f1f071f0f0f0

def z1227 : W := mkw 0x04332220ac1a3030 0xc10cc8882b068c0c 0xe4772727fe3b3033 0xb91dc9c9ff8ecc0c

def z1228 : W := mkw 0x0185848104828000 0x006161204120a000 0x93870701c7c00000 0x24e1c1c071f00000

def z1229 : W := mkw 0x06c905924f7f33b8 0xc1b2416493dfccee 0x3f8800d807ff33fc 0x4fe2003601ffccff

def z1230 : W := mkw 0x0985858346c3c3c3 0x02616160d1b0f0f0 0xfb8707c1c7c3c3c2 0x7ee1c1f071f0f0f0

def z1231 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0xfffff8d807fffccd 0xfffffe3601ffff33

def z1232 : W := mkw 0x84332322ee1b7776 0xe10cc8c8bb86dddd 0xec7f27fffe3fffff 0xfb1fc9ffff8fffff

def z1233 : W := mkw 0x040101024e1b3330 0xc10040409386cccc 0x2c000000063f33fc 0x0b000000018fccff

def z1234 : W := mkw 0x027a3220a0000000 0x009e8c8828000000 0xc07f3f27f8000003 0xb01fcfc9fe000000

def z1235 : W := mkw 0x13fefefdb1640088 0x04ffbfbf6c590022 0xfffffffffffc00cf 0xffffffffffff0033

def z1236 : W := mkw 0x93fefefdb0004446 0x24ffbfbf6c001111 0xfffffffff807fccf 0xfffffffffe01ff33

def z1237 : W := mkw 0x00322220a0000000 0x000c888828000000 0xc07f27fff8000003 0xf01fc9fffe000000

def z1238 : W := mkw 0x8985cdcf56c3c7c7 0x22617373d5b0f1f1 0xff8fffdfc7c7ffcf 0xffe3fff7f1f1fff3

def z1239 : W := mkw 0x0105810246838300 0x0041604091a0e0c0 0xf3870707c7c30303 0x3ce1c1c1f1f0c0c0

def z1240 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb87c707c7c3c001 0x7ee1f1c1f1f0f000

def z1241 : W := mkw 0x0105810046828200 0x0041604011a0a080 0x93870701c7c00000 0x24e1c1c071f00000

def z1242 : W := mkw 0x136fb001a5b6a800 0x04dbec00696daa00 0xfffff801c7fffc01 0xfffffe0071ffff00

def z1243 : W := mkw 0x00322220a0000000 0x000c888828000000 0xec7f27fff80403ff 0xfb1fc9fffe0100ff

def z1244 : W := mkw 0x0985c5c74ec3d3d3 0x82617171d3b0f4f4 0xff8fffe7ffc7fff3 0xffe3fff9fff1fffc

def z1245 : W := mkw 0x04332322ee1b7372 0xc10cc8c8bb86dcdc 0xec772727fe3bf3f3 0xbb1dc9c9ff8efcfc

def z1246 : W := mkw 0x93fefefdb0004446 0x24ffbfbf6c001111 0xd3fffffff800cc03 0xf4fffffffe003300

def z1247 : W := mkw 0x927a3a38b92c143c 0xa49e8e8e2e4b050f 0x04783838383c3c3c 0x811e0e0e0e0f0f0f

def z1248 : W := mkw 0x00322220a0000000 0x000c888828000000 0xec7fff27f807fc03 0xfb1fffc9fe01ff00

def z1249 : W := mkw 0x0985858146c28281 0x0261616051b0a0a0 0xbb870701c7c3c000 0x2ee1c1c071f0f000

def z1250 : W := mkw 0x037eb220a0000000 0x00dfac8828000000 0xd3f72727f8000003 0xb4fdc9c9fe000000

def z1251 : W := mkw 0x13fefefdb13c2828 0x04ffbfbf6c4f0a0a 0xd7fffffff83c3c3f 0xf5fffffffe0f0f0f

def z1252 : W := mkw 0x867a2a38b93c343c 0xe19e8a8e2e4f0d0f 0x04783838383c3c3c 0x811e0e0e0e0f0f0f

def z1253 : W := mkw 0x0000000208011110 0x8000000082004444 0x6c08f8fe3807ffff 0xdb023e3f8e01ffff

def z1254 : W := mkw 0x898585834ec3d7d7 0xa2616160d3b0f5f5 0xbf870701c7c7fffc 0x2fe1c1c071f1ffff

def z1255 : W := mkw 0x03fee6f5a0000000 0x00ffb9bd68000000 0xd3ffe7fff8000003 0xf4fff9fffe000000

def z1256 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xfb87c7ffc7c3c3ff 0x7ee1f1fff1f0f0ff

def z1257 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x138ffffff8000003 0x44e3fffffe000000

def z1258 : W := mkw 0x0185cccd14828000 0x006173334520a000 0xff8fffffffc7fc03 0xffe3fffffff1ff00

def z1259 : W := mkw 0x0985cdcf56c3c3c3 0x02617373d5b0f0f0 0xfb8fdfdfc7c3c3c3 0x7ee3f7f7f1f0f0f0

def z1260 : W := mkw 0x036fb00005b6a800 0x00dbec00016daa00 0x9bfff80007fffc01 0x66fffe0001ffff00

def z1261 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xec772727fe3fff33 0xbb1dc9c9ff8fffcc

def z1262 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xd3fffffff80003ff 0xf4fffffffe0000ff

def z1263 : W := mkw 0x04332322ee9bbb30 0xc10cc8c8bba6eecc 0xe4772727fe3bff33 0xb91dc9c9ff8effcc

def z1264 : W := mkw 0x067a2230a13c2028 0x419e888c284f080a 0x04780038003c003c 0x811e000e000f000f

def z1265 : W := mkw 0x84904ffefa4957fe 0xe12413ffbe9255ff 0x000007fff80003fe 0x000001fffe0000ff

def z1266 : W := mkw 0x0985cdcf56c3c3c3 0x02617373d5b0f0f0 0xff8fffffffc7c3ff 0xffe3fffffff1f0ff

def z1267 : W := mkw 0x13ccdcdd11a48800 0x04f3373744692200 0x1388d8d801c00000 0x44e2363600700000

def z1268 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0x80772727fe3b3333 0x201dc9c9ff8ecccc

def z1269 : W := mkw 0x03fef6e5a0000000 0x00ffbdb968000000 0xd3ffffe7f8000003 0xf4fffff9fe000000

def z1270 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xdbfffffff80400cf 0xf6fffffffe010033

def z1271 : W := mkw 0x067a3230a93c3838 0xc19e8c8c2a4f0e0e 0x04783838383c3c3c 0x811e0e0e0e0f0f0f

def z1272 : W := mkw 0x041103224e1b3330 0xc10440c89386cccc 0x24700020063b3330 0x891c0008018ecccc

def z1273 : W := mkw 0x13fefefdb1240000 0x04ffbfbf6c490000 0xdbfffffff9c40003 0xf6fffffffe710000

def z1274 : W := mkw 0x067a3222a93d3930 0xc19e8c88aa4f4e4c 0x6c78f826383fff33 0xdb1e3e098e0fffcc

def z1275 : W := mkw 0x93ccdcdd11a4cc46 0x24f3373744693311 0x1b88d8d801c4cccc 0x46e2363600713333

def z1276 : W := mkw 0x04332320e61a2220 0x410cc8c839868888 0xe4772727fe3b3003 0xb91dc9c9ff8ecc00

def z1277 : W := mkw 0x02d807b0036c02a8 0x00b601ec00db00aa 0x97f807f807fc03fe 0xa5fe01fe01ff00ff

def z1278 : W := mkw 0x0985858346c38381 0x02616160d1b0e0e0 0x93870707c7c30001 0x24e1c1c1f1f0c000

def z1279 : W := mkw 0x0184c5c7024143c2 0x00613171c09050f0 0xfb87c7c7c7c3c3c3 0x7ee1f1f1f1f0f0f0

def z1280 : W := mkw 0x0985c5c546c2c2c3 0x0261717151b0b0b0 0xfb87c7c1c7c3c0c1 0x7ee1f1f071f0f030

def z1281 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xfff72727fffb3333 0xfffdc9c9fffecccc

def z1282 : W := mkw 0x074d91024fbfbb30 0xc1d3644093efeecc 0x3f88d80007ffff30 0x4fe2360001ffffcc

def z1283 : W := mkw 0x00322220a0000000 0x000c888828000000 0xe4772727f8033003 0xb91dc9c9fe00cc00

def z1284 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xff8fffffc7c7ffff 0xffe3fffff1f1ffff

def z1285 : W := mkw 0x0881058246c3c3c3 0x0220416091b0f0f0 0xfb8707c7c7c3c3c3 0x7ee1c1f1f1f0f0f0

def z1286 : W := mkw 0x00326264a0000000 0x000c989928000000 0xc077e7e7f8000003 0xf01df9f9fe000000

def z1287 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0x93ff3ffff8000002 0xa4ffcffffe000000

def z1288 : W := mkw 0x04332320e61a2220 0x410cc8c839868888 0x80772707fe380001 0x201dc9c1ff8e0000

def z1289 : W := mkw 0x10326a6db0000000 0x040c9a9b6c000000 0xc0772727f8000003 0xb01dc9c9fe000000

def z1290 : W := mkw 0x13fefefdb16c00a8 0x04ffbfbf6c5b002a 0xdffffffff9fc00ff 0xf7fffffffe7f003f

def z1291 : W := mkw 0x0985c5c546c2c2c3 0x0261717151b0b0b0 0x9387c701c7c0c000 0x24e1f1c071f03000

def z1292 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xf38707c7c7c303c3 0x3ce1c1f1f1f0c0f0

def z1293 : W := mkw 0x040101024e133310 0xc10040409384ccc4 0x2000000006033300 0x080000000180ccc0

def z1294 : W := mkw 0x1bfefefdb04040c3 0x06ffbfbf6c101030 0xd3fffffff80000c3 0xf4fffffffe000030

def z1295 : W := mkw 0x027a3220a1342800 0x009e8c88284d0a00 0xc47f3f27f83c3c03 0xb11fcfc9fe0f0f00

def z1296 : W := mkw 0x04332322ee1b3330 0xc10cc8c8bb86cccc 0xe47727fffe3b33ff 0xb91dc9ffff8eccff

def z1297 : W := mkw 0x0985858346c3c3c3 0x02616160d1b0f0f0 0x93870701c7c003c0 0x24e1c1c071f000f0

def z1298 : W := mkw 0x13fefefdb0080028 0x04ffbfbf6c02000a 0xd3fffffff800003f 0xf4fffffffe00000f

def z1299 : W := mkw 0x0985cdcf5ec3d3d3 0x82617373d7b0f4f4 0xff8fffffffc3f3f3 0xffe3fffffff0fcfc

def z1300 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xff87c7c7c7c7ffc3 0x7fe1f1f1f1f1fff0

def z1301 : W := mkw 0x0985d5c746c3cbc3 0x02617571d1b0f2f0 0xfb87dfc7c7c3cfc3 0x7ee1f7f1f1f0f3f0

def z1302 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xfb8fffdfffc7ffcf 0x7ee3fff7fff1fff3

def z1303 : W := mkw 0x076fb000e5b6a800 0x41dbec00396daa00 0xfffff801c7fffc01 0xfffffe0071ffff00

def z1304 : W := mkw 0x10323a28b0000000 0x040c8e8a2c000000 0xc0773f27f8000003 0xb01dcfc9fe000000

def z1305 : W := mkw 0x00322220a0000000 0x000c888828000000 0xe4772727f8000333 0xb91dc9c9fe0000cc

def z1306 : W := mkw 0x11b6fefdb0000000 0x046dbfbf6c000000 0xc077fffff8000003 0xb01dfffffe000000

def z1307 : W := mkw 0x8985cdcf5ec3d7d7 0xa2617373d7b0f5f5 0xff87e7ffffc3f3ff 0xffe1f9fffff0fcff

def z1308 : W := mkw 0x13fefefdb0102800 0x04ffbfbf6c040a00 0xd3fffffff8003c03 0xf4fffffffe000f00

def z1309 : W := mkw 0x0985c5c746c3c3c3 0x02617171d1b0f0f0 0xbb87c707c7c3c3c1 0x2ee1f1c1f1f0f0f0

def z1310 : W := mkw 0x13fefefdb0808800 0x04ffbfbf6c202200 0xd3fffffff800cc03 0xf4fffffffe003300

def z1311 : W := mkw 0x066b31024f3f3b30 0xc19acc4093cfcecc 0x24783800063f3f30 0x891e0e00018fcfcc

def z1312 : W := mkw 0x13fefefdb0000000 0x04ffbfbf6c000000 0xf7fffffff8000333 0xfdfffffffe0000cc

def z1313 : W := mkw 0x040101024f3f3338 0xc100404093cfccce 0x24000000063f333c 0x09000000018fcccf

def z1314 : W := mkw 0x90904fffba4957fe 0xa42413ffee9255ff 0x000007fff80003fe 0x000001fffe0000ff

def z1315 : W := mkw 0x1bccdcdd11e4c8c3 0x06f3373744793230 0x1b88d8d801c4ccc0 0x46e2363600713330

def z1316 : W := mkw 0x009007b0024802a8 0x002401ec009200aa 0xfff007f807f803fe 0xfffc01fe01fe00ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z8,z9,z3,z4,z6]),(0,[z1,z7,z10,z2,z3,z4,z6]),(0,[z1,z7,z11,z2,z3,z12,z6])],[(0,[z1,z7,z13,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z4,z6,z15]),(0,[z1,z7,z2,z16,z17,z4,z6]),(0,[z18,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z3,z19,z4,z6]),(0,[z1,z7,z2,z20,z21,z4,z6])],[(0,[z22,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z23,z4,z6]),(0,[z1,z7,z24,z2,z3,z4,z6])],[(0,[z1,z7,z2,z16,z4,z6,z25]),(0,[z1,z7,z2,z26,z3,z4,z6]),(0,[z1,z7,z8,z2,z3,z4,z27]),(0,[z1,z7,z2,z28,z16,z4,z6])],[(0,[z1,z7,z2,z3,z29,z4,z6]),(0,[z1,z7,z2,z3,z30,z6,z31]),(0,[z1,z7,z2,z4,z6,z14,z32])],[(0,[z1,z7,z2,z3,z4,z6,z33]),(1,[z1,z7,z34,z3,z4,z6]),(0,[z35,z1,z7,z2,z21,z4,z6]),(0,[z1,z36,z7,z2,z3,z4,z6]),(1,[z1,z7,z37,z3,z4,z6])],[(0,[z1,z7,z38,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z39,z6]),(0,[z1,z7,z2,z3,z40,z4,z6]),(1,[z1,z7,z2,z16,z4,z6])]],
   [[(0,[z41,z0,z1,z2,z3,z4,z6]),(0,[z0,z7,z42,z2,z3,z4,z6]),(1,[z1,z7,z2,z3,z43,z6]),(0,[z1,z7,z2,z3,z4,z44,z6]),(0,[z1,z7,z2,z3,z4,z6,z45])],[(0,[z1,z7,z46,z2,z3,z4,z6]),(0,[z47,z1,z7,z2,z3,z4,z6]),(0,[z48,z1,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z20,z3,z6]),(0,[z1,z7,z11,z8,z2,z3,z6]),(0,[z50,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z51,z3,z4,z6]),(0,[z1,z7,z2,z4,z52,z6,z53])],[(1,[z54,z7,z9,z3,z4,z6]),(0,[z1,z7,z2,z9,z4,z6,z14]),(1,[z55,z7,z13,z3,z4,z6]),(0,[z56,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z57,z2,z3,z4,z6]),(0,[z1,z7,z2,z58,z3,z4,z6]),(0,[z1,z7,z2,z4,z6,z14,z14])],[(0,[z59,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z60,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z61,z6]),(0,[z1,z7,z2,z4,z62,z6,z14])],[(0,[z63,z1,z64,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z65,z6])],[(0,[z1,z7,z66,z2,z67,z3,z6]),(1,[z49,z1,z64,z7,z3,z6]),(0,[z1,z7,z68,z2,z3,z4,z6]),(0,[z49,z1,z7,z8,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z52,z6])],[(0,[z1,z7,z2,z69,z4,z6,z14]),(1,[z70,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z30,z4,z6,z14]),(1,[z1,z7,z2,z3,z71,z6]),(0,[z72,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z4,z6,z14])]],
   [[(1,[z73,z7,z2,z3,z4,z6]),(0,[z1,z7,z74,z2,z3,z4,z6]),(0,[z75,z49,z1,z7,z2,z3,z6]),(1,[z1,z7,z11,z2,z16,z6])],[(0,[z76,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z77,z2,z3,z4,z6]),(0,[z1,z7,z11,z2,z3,z17,z6]),(0,[z78,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z4,z79,z6,z14]),(0,[z1,z7,z2,z16,z19,z4,z6]),(1,[z1,z7,z80,z3,z4,z6]),(0,[z81,z1,z7,z2,z4,z6,z14]),(0,[z82,z49,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z83,z21,z4,z6]),(0,[z1,z7,z2,z3,z4,z84,z6]),(0,[z85,z1,z7,z11,z2,z3,z6]),(0,[z1,z86,z7,z2,z3,z4,z6])],[(0,[z87,z1,z7,z2,z3,z4,z6]),(0,[z88,z1,z7,z2,z3,z4,z89]),(0,[z56,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z11,z57,z2,z3,z6]),(0,[z1,z7,z57,z2,z16,z4,z6]),(0,[z1,z7,z11,z2,z3,z21,z6]),(0,[z1,z7,z2,z3,z90,z4,z6])],[(0,[z1,z42,z2,z3,z4,z6,z25]),(0,[z88,z41,z7,z2,z3,z4,z6]),(0,[z91,z1,z7,z2,z3,z4,z89]),(0,[z1,z7,z2,z3,z92,z4,z6]),(0,[z1,z7,z2,z93,z3,z4,z6])],[(0,[z1,z7,z2,z3,z4,z6,z94]),(0,[z1,z7,z2,z3,z4,z95,z6]),(0,[z49,z1,z7,z2,z16,z3,z6]),(0,[z96,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z3,z97,z4,z6]),(0,[z98,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z99,z6]),(1,[z1,z7,z66,z2,z3,z6]),(0,[z1,z2,z3,z4,z5,z6,z25]),(1,[z1,z7,z57,z20,z4,z6])],[(0,[z49,z0,z1,z7,z2,z3,z6])]],
   [[(0,[z1,z7,z2,z3,z4,z6,z100]),(1,[z1,z7,z2,z3,z101,z6]),(0,[z102,z1,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z57,z3,z4,z6]),(0,[z103,z1,z7,z2,z3,z4,z6]),(0,[z72,z1,z7,z2,z3,z6,z27]),(0,[z1,z7,z2,z3,z4,z6,z31])],[(0,[z104,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z105,z2,z3,z4,z6]),(0,[z1,z106,z7,z2,z3,z4,z6]),(0,[z81,z1,z7,z57,z2,z4,z6]),(0,[z1,z7,z2,z3,z107,z4,z6])],[(0,[z1,z108,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z109,z67,z4,z6]),(0,[z1,z7,z11,z2,z3,z6,z25]),(0,[z1,z7,z2,z3,z4,z6,z110]),(1,[z111,z1,z7,z2,z62,z6]),(0,[z112,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z6,z113,z14])],[(0,[z1,z114,z7,z2,z9,z3,z6]),(0,[z87,z1,z7,z2,z16,z4,z6]),(0,[z115,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z116,z4,z6]),(0,[z1,z117,z7,z2,z4,z6,z14]),(0,[z118,z1,z7,z2,z3,z4,z6]),(0,[z82,z1,z7,z2,z3,z119,z6]),(0,[z1,z7,z2,z3,z4,z120,z6]),(0,[z1,z7,z2,z4,z121,z6,z122])],[(0,[z1,z7,z11,z2,z123,z3,z6]),(0,[z1,z124,z7,z11,z2,z3,z6]),(0,[z1,z125,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z126,z4,z6])],[(0,[z127,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z128,z3,z129,z6]),(0,[z1,z7,z11,z2,z128,z3,z6]),(0,[z1,z7,z2,z16,z130,z4,z6]),(0,[z1,z7,z131,z2,z3,z4,z6])],[(0,[z1,z7,z2,z132,z4,z6,z14]),(0,[z1,z7,z133,z2,z3,z4,z6]),(1,[z56,z1,z7,z83,z4,z6]),(0,[z111,z1,z7,z2,z83,z4,z6]),(0,[z1,z7,z2,z3,z134,z4,z6]),(0,[z1,z7,z2,z128,z3,z21,z6]),(0,[z1,z7,z2,z16,z4,z52,z6])],[(0,[z41,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z3,z135,z4,z6]),(0,[z136,z1,z7,z2,z4,z6,z14])]],
   [[(0,[z137,z1,z7,z2,z3,z4,z6]),(0,[z138,z1,z7,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z6,z139]),(0,[z1,z64,z7,z140,z3,z4,z6]),(0,[z141,z49,z1,z7,z2,z3,z6]),(0,[z49,z1,z7,z3,z4,z6,z27]),(1,[z1,z7,z2,z142,z4,z6])],[(0,[z143,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z144,z6]),(0,[z1,z7,z11,z2,z67,z3,z6]),(0,[z49,z1,z7,z2,z3,z69,z6]),(0,[z1,z7,z2,z3,z30,z4,z6]),(1,[z85,z1,z7,z2,z4,z14])],[(0,[z81,z1,z7,z2,z123,z4,z6]),(0,[z145,z1,z7,z2,z3,z4,z6]),(0,[z1,z146,z7,z2,z3,z4,z6])],[(0,[z87,z1,z7,z2,z21,z4,z6]),(0,[z1,z7,z2,z3,z79,z129,z6]),(0,[z1,z7,z2,z3,z4,z6,z147]),(0,[z1,z7,z2,z4,z5,z6,z148]),(0,[z1,z7,z2,z3,z4,z149,z6]),(0,[z1,z7,z2,z16,z90,z4,z6])],[(0,[z1,z7,z2,z3,z4,z150,z6]),(0,[z1,z7,z2,z151,z3,z4,z6]),(0,[z152,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z8,z67,z3,z4,z6]),(0,[z1,z7,z2,z3,z153,z4,z6])],[(0,[z1,z7,z11,z2,z3,z6,z14]),(0,[z1,z7,z2,z3,z4,z62,z6])],[(0,[z75,z1,z7,z2,z3,z4,z6]),(0,[z154,z1,z7,z2,z3,z4,z6]),(0,[z155,z1,z7,z2,z4,z6,z14]),(1,[z88,z7,z2,z3,z4,z156]),(0,[z82,z1,z7,z2,z3,z4,z25]),(0,[z1,z7,z2,z21,z4,z6,z14]),(0,[z1,z7,z2,z157,z3,z4,z6]),(0,[z1,z7,z3,z4,z52,z6,z158])],[(0,[z1,z7,z2,z159,z4,z6,z14]),(0,[z1,z160,z7,z2,z3,z4,z6]),(0,[z161,z49,z1,z7,z2,z3,z6]),(0,[z49,z1,z7,z2,z3,z162,z6]),(0,[z1,z7,z2,z3,z4,z163,z6])]],
   [[(0,[z164,z41,z1,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z165,z6]),(0,[z166,z1,z7,z2,z3,z4,z6]),(1,[z76,z1,z7,z2,z4,z6]),(0,[z1,z7,z140,z8,z3,z4,z6]),(0,[z82,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z128,z21,z6]),(0,[z1,z7,z2,z3,z4,z167,z6]),(0,[z85,z1,z7,z2,z3,z4,z6])],[(0,[z168,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z169,z4,z6]),(0,[z1,z7,z170,z2,z3,z4,z6]),(0,[z1,z7,z171,z2,z3,z4,z6]),(0,[z1,z7,z172,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z11,z2,z58,z3,z6]),(0,[z1,z7,z2,z16,z107,z4,z6]),(0,[z173,z1,z7,z2,z3,z174,z6])],[(0,[z1,z7,z2,z3,z4,z175,z6]),(0,[z1,z7,z2,z3,z176,z4,z6]),(0,[z1,z7,z177,z2,z3,z4,z6]),(0,[z49,z1,z7,z11,z2,z3,z6]),(0,[z178,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z179,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z6,z180,z27]),(0,[z1,z7,z2,z3,z21,z4,z6]),(0,[z1,z7,z181,z2,z4,z6,z14])],[(0,[z0,z1,z42,z2,z3,z4,z6]),(0,[z35,z1,z7,z2,z69,z4,z6]),(0,[z1,z7,z3,z182,z4,z129,z6]),(0,[z1,z183,z7,z2,z3,z4,z6]),(0,[z82,z1,z7,z2,z3,z184,z6]),(0,[z1,z7,z2,z3,z4,z6,z185])],[(0,[z186,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z187,z2,z3,z4,z6]),(1,[z49,z1,z7,z2,z3,z6])],[(0,[z1,z7,z42,z2,z4,z6,z14]),(0,[z41,z1,z124,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z188]),(0,[z155,z1,z7,z57,z2,z4,z6]),(0,[z1,z7,z2,z189,z3,z4,z6]),(0,[z1,z7,z11,z2,z3,z39,z6]),(1,[z1,z7,z2,z190,z4,z6])],[(1,[z91,z7,z2,z3,z4,z89]),(0,[z191,z1,z7,z2,z3,z4,z6]),(0,[z75,z1,z7,z2,z16,z4,z6]),(0,[z173,z1,z7,z2,z192,z4,z6])],[(0,[z1,z193,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z194]),(0,[z49,z1,z7,z195,z2,z3,z6]),(0,[z1,z7,z2,z16,z4,z121,z6])]],
   [[(0,[z1,z7,z2,z196,z3,z4,z6]),(0,[z82,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z2,z4,z6,z25,z14]),(0,[z197,z1,z7,z2,z3,z4,z6]),(0,[z198,z1,z7,z2,z3,z4,z6]),(0,[z49,z1,z199,z7,z2,z3,z6]),(0,[z1,z7,z2,z200,z3,z4,z6])],[(0,[z1,z7,z2,z3,z201,z4,z6]),(0,[z1,z7,z2,z3,z4,z79,z6]),(1,[z202,z1,z7,z3,z4,z6]),(0,[z1,z7,z11,z3,z17,z4,z6])],[(0,[z1,z7,z2,z3,z4,z6,z156]),(0,[z203,z1,z7,z2,z3,z4,z6]),(0,[z1,z124,z7,z2,z3,z4,z6])],[(0,[z111,z87,z1,z7,z2,z4,z6]),(0,[z1,z7,z3,z204,z4,z79,z6]),(0,[z1,z7,z2,z205,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z206,z6]),(0,[z1,z7,z8,z2,z3,z4,z121])],[(0,[z1,z7,z2,z3,z207,z4,z6]),(0,[z1,z7,z2,z3,z19,z129,z6]),(0,[z1,z7,z2,z3,z4,z208,z6]),(0,[z209,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z11,z2,z3,z52,z6])],[(0,[z81,z1,z7,z2,z3,z210,z6]),(0,[z1,z7,z2,z3,z211,z4,z6]),(1,[z1,z7,z2,z3,z119,z6]),(0,[z1,z7,z2,z3,z212,z4,z6]),(0,[z1,z7,z2,z20,z3,z4,z6]),(0,[z213,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z4,z62,z6])],[(1,[z155,z7,z2,z159,z4,z6]),(0,[z1,z7,z214,z2,z3,z4,z6]),(0,[z215,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z4,z5,z6,z14]),(0,[z1,z7,z2,z3,z4,z6,z216]),(0,[z1,z7,z2,z3,z4,z217,z6]),(0,[z218,z1,z7,z2,z4,z6,z14]),(0,[z191,z1,z7,z2,z16,z4,z6])],[(0,[z1,z7,z2,z3,z219,z4,z6]),(0,[z1,z64,z7,z2,z16,z4,z6]),(0,[z111,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z8,z2,z3,z4,z6])]],
   [[(0,[z220,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z221,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z222,z4,z6]),(1,[z72,z1,z7,z2,z3,z6]),(0,[z223,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z3,z224,z4,z6]),(0,[z0,z1,z7,z2,z16,z4,z6]),(0,[z225,z1,z7,z2,z4,z79,z6])],[(0,[z1,z7,z2,z3,z4,z226,z6]),(0,[z227,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z228,z4,z6]),(0,[z1,z7,z2,z3,z4,z229,z6]),(0,[z1,z7,z140,z3,z4,z6,z27]),(0,[z1,z7,z230,z2,z3,z4,z6]),(0,[z1,z7,z231,z2,z3,z4,z6])],[(0,[z41,z7,z2,z3,z4,z89,z6]),(1,[z54,z49,z1,z7,z3,z6]),(0,[z55,z1,z7,z3,z17,z4,z6]),(0,[z232,z7,z2,z3,z19,z4,z6]),(0,[z1,z7,z11,z2,z3,z19,z6]),(0,[z1,z7,z11,z2,z2,z3,z6]),(0,[z1,z7,z11,z2,z3,z174,z6]),(0,[z1,z7,z2,z3,z142,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z158])],[(0,[z1,z7,z2,z169,z9,z4,z6]),(0,[z1,z7,z2,z3,z233,z4,z6]),(0,[z1,z7,z234,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z182,z4,z6]),(0,[z235,z1,z7,z2,z3,z4,z6]),(0,[z49,z1,z124,z7,z2,z3,z6])],[(0,[z161,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z236,z6]),(0,[z63,z49,z1,z7,z2,z3,z6]),(0,[z237,z1,z7,z2,z3,z4,z6]),(0,[z73,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z20,z16,z4,z6]),(0,[z1,z7,z2,z3,z52,z6,z31])],[(0,[z1,z7,z11,z13,z2,z3,z6]),(0,[z1,z7,z2,z3,z238,z4,z6]),(0,[z88,z1,z239,z2,z3,z4,z6]),(0,[z1,z7,z11,z2,z3,z240,z6]),(0,[z1,z7,z2,z4,z6,z241,z14]),(0,[z242,z1,z7,z2,z3,z4,z6])],[(0,[z49,z1,z7,z2,z132,z3,z6]),(0,[z1,z7,z2,z3,z4,z243,z6]),(0,[z82,z1,z7,z2,z244,z4,z6]),(0,[z1,z7,z11,z2,z4,z6,z14]),(0,[z1,z7,z8,z2,z16,z4,z6])]],
   [[(0,[z1,z7,z2,z3,z245,z4,z6]),(0,[z1,z7,z2,z246,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z247,z6]),(0,[z49,z1,z7,z2,z3,z89,z6]),(0,[z1,z7,z248,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z249,z4,z6]),(0,[z82,z118,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z250])],[(0,[z54,z1,z7,z3,z17,z4,z6]),(0,[z1,z7,z2,z16,z4,z79,z6]),(0,[z49,z1,z64,z7,z2,z3,z6]),(0,[z1,z7,z2,z251,z3,z4,z6])],[(0,[z252,z1,z7,z2,z3,z4,z6]),(0,[z253,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z101,z4,z6]),(0,[z1,z7,z2,z3,z4,z254,z6]),(0,[z1,z7,z34,z2,z3,z4,z6]),(0,[z255,z1,z7,z2,z3,z4,z6]),(0,[z256,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z3,z257,z4,z6]),(0,[z1,z7,z2,z258,z3,z4,z6]),(1,[z259,z1,z7,z3,z4,z6]),(0,[z1,z7,z260,z2,z3,z4,z6]),(0,[z111,z1,z7,z2,z128,z4,z6])],[(0,[z1,z124,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z261,z3,z4,z6])],[(0,[z1,z7,z2,z3,z4,z262,z6]),(0,[z1,z7,z2,z3,z263,z4,z6]),(0,[z264,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z129,z6,z31]),(1,[z1,z7,z2,z3,z184,z6]),(0,[z1,z7,z2,z20,z3,z71,z6]),(0,[z1,z7,z11,z2,z3,z121,z6]),(0,[z1,z7,z265,z128,z3,z4,z6]),(0,[z1,z7,z2,z3,z174,z4,z6])],[(0,[z164,z0,z7,z2,z3,z4,z6]),(0,[z266,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z128,z3,z19,z6]),(0,[z1,z7,z2,z128,z3,z30,z6])],[(0,[z267,z1,z7,z2,z3,z4,z6]),(0,[z268,z1,z7,z2,z3,z4,z6])]],
   [[(0,[z269,z1,z7,z2,z3,z19,z6]),(0,[z232,z1,z7,z2,z3,z19,z6]),(0,[z82,z1,z2,z3,z4,z6,z25]),(0,[z49,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z2,z4,z6,z27,z14])],[(0,[z1,z7,z2,z3,z4,z270,z6]),(0,[z1,z7,z2,z3,z4,z271,z6]),(1,[z272,z1,z2,z3,z4,z6]),(0,[z81,z1,z7,z2,z3,z273,z6]),(0,[z1,z7,z3,z83,z17,z4,z6]),(0,[z49,z1,z7,z2,z3,z6,z27]),(0,[z1,z7,z2,z3,z4,z6,z274]),(0,[z1,z7,z2,z3,z4,z6,z275]),(0,[z1,z7,z2,z251,z16,z4,z6])],[(0,[z1,z7,z276,z2,z9,z3,z6]),(0,[z111,z1,z7,z2,z3,z79,z6]),(1,[z1,z7,z2,z277,z4,z6]),(0,[z278,z1,z7,z2,z3,z4,z6]),(0,[z56,z1,z7,z2,z20,z4,z6]),(0,[z1,z7,z57,z2,z20,z4,z6])],[(0,[z164,z1,z7,z2,z4,z6,z14]),(0,[z56,z155,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z3,z279,z4,z6]),(0,[z1,z7,z2,z3,z4,z280,z6]),(0,[z1,z7,z11,z2,z3,z62,z6]),(0,[z136,z1,z7,z8,z3,z4,z6])],[(0,[z269,z1,z7,z2,z4,z6,z14]),(0,[z232,z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z21,z4,z62,z6])],[(0,[z1,z7,z2,z3,z4,z281,z6]),(0,[z282,z1,z7,z2,z3,z4,z6]),(0,[z49,z155,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z283,z3,z4,z6]),(0,[z49,z1,z7,z2,z3,z83,z6])],[(0,[z1,z284,z7,z2,z3,z4,z6]),(1,[z1,z124,z2,z3,z4,z5]),(0,[z1,z7,z2,z3,z4,z6,z285]),(0,[z173,z1,z7,z2,z128,z3,z6]),(0,[z50,z1,z7,z2,z3,z6,z14])],[(0,[z1,z7,z286,z2,z3,z4,z6]),(0,[z54,z1,z7,z2,z4,z6,z14]),(0,[z63,z1,z2,z67,z3,z4,z6]),(0,[z1,z287,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z69,z4,z6]),(0,[z1,z7,z2,z3,z4,z288,z6])]],
   [[(0,[z289,z1,z7,z2,z3,z4,z6]),(0,[z164,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z3,z4,z273,z6]),(0,[z1,z7,z290,z11,z2,z3,z6]),(0,[z291,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z292,z3,z4,z6]),(0,[z1,z7,z293,z2,z3,z4,z6]),(1,[z1,z7,z2,z294,z4,z6]),(0,[z49,z1,z7,z2,z3,z295,z6])],[],[(1,[z1,z7,z276,z2,z3,z6]),(0,[z63,z1,z7,z2,z3,z4,z6]),(1,[z49,z1,z7,z2,z16,z6]),(1,[z1,z7,z2,z16,z4,z14])],[],[(0,[z1,z7,z296,z2,z3,z4,z6]),(0,[z297,z1,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z9,z3,z6]),(0,[z259,z1,z7,z3,z4,z79,z6]),(0,[z1,z7,z2,z3,z228,z4,z6]),(0,[z298,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z299]),(0,[z85,z49,z1,z7,z2,z3,z6]),(0,[z300,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z123,z4,z6,z14]),(0,[z1,z301,z7,z2,z3,z4,z6]),(0,[z56,z1,z7,z3,z83,z4,z6]),(0,[z168,z49,z1,z7,z2,z3,z6]),(0,[z1,z7,z11,z2,z302,z3,z6]),(0,[z1,z7,z3,z4,z121,z6,z27]),(1,[z1,z7,z2,z3,z6,z303])],[(1,[z1,z7,z2,z3,z238,z6]),(1,[z1,z7,z2,z4,z6,z122])]],
   [[(0,[z88,z1,z7,z2,z3,z304,z6]),(0,[z1,z305,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z306]),(0,[z111,z1,z7,z2,z4,z62,z6])],[(0,[z1,z7,z2,z3,z4,z6,z307]),(0,[z7,z2,z3,z19,z4,z79,z6]),(1,[z1,z7,z2,z244,z4,z6]),(0,[z1,z7,z2,z3,z308,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z309])],[(0,[z310,z1,z7,z2,z3,z4,z6]),(0,[z311,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z140,z2,z3,z4,z6]),(0,[z81,z1,z7,z11,z2,z3,z6]),(1,[z118,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z93,z4,z5,z6]),(0,[z1,z312,z7,z2,z3,z4,z6])],[(0,[z63,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z2,z313,z3,z4,z6]),(0,[z1,z7,z314,z2,z3,z4,z6])],[(0,[z315,z1,z7,z2,z4,z6,z14]),(0,[z316,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z57,z3,z17,z4,z6]),(0,[z1,z7,z11,z2,z58,z4,z6]),(0,[z1,z7,z2,z4,z6,z317,z14])],[(0,[z1,z7,z2,z3,z3,z4,z6]),(0,[z318,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z19,z174,z6]),(0,[z1,z7,z57,z20,z3,z4,z6]),(0,[z198,z49,z1,z7,z2,z3,z6]),(0,[z136,z1,z7,z3,z4,z6,z27]),(0,[z1,z7,z2,z3,z4,z6,z319])],[(0,[z1,z7,z2,z3,z320,z4,z6]),(0,[z1,z7,z2,z3,z4,z162,z6]),(0,[z1,z7,z2,z3,z4,z6,z180])],[(0,[z1,z7,z2,z3,z321,z4,z6]),(0,[z1,z7,z13,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z322,z6]),(0,[z1,z7,z133,z2,z67,z3,z6]),(0,[z1,z7,z2,z323,z3,z4,z6]),(0,[z1,z7,z2,z324,z3,z4,z6]),(0,[z1,z325,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z192,z4,z6])]],
   [[(0,[z1,z326,z7,z2,z3,z4,z6]),(0,[z327,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z328,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z173,z1,z7,z2,z329,z4,z6])],[(0,[z49,z91,z1,z7,z2,z3,z6]),(1,[z1,z117,z2,z3,z129,z6]),(0,[z330,z1,z7,z2,z3,z4,z6]),(0,[z315,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z3,z4,z6,z331]),(0,[z1,z7,z2,z4,z162,z6,z14]),(1,[z1,z7,z11,z2,z6,z14]),(0,[z1,z7,z2,z126,z3,z4,z6]),(0,[z332,z1,z7,z2,z3,z4,z6]),(0,[z333,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z334,z3,z4,z6]),(0,[z335,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z336,z6])],[(0,[z337,z1,z7,z2,z3,z4,z6]),(0,[z88,z1,z171,z2,z3,z4,z6]),(0,[z338,z1,z7,z2,z3,z4,z6]),(1,[z63,z49,z1,z7,z3,z6]),(0,[z1,z140,z2,z67,z3,z4,z6]),(0,[z35,z111,z1,z7,z2,z4,z6]),(0,[z1,z117,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z3,z4,z339,z6]),(0,[z1,z7,z2,z3,z340,z4,z6]),(0,[z341,z1,z7,z2,z3,z4,z6])],[(0,[z7,z42,z2,z3,z4,z6,z156]),(0,[z1,z7,z342,z2,z3,z4,z6]),(0,[z269,z1,z7,z2,z3,z79,z6]),(0,[z1,z7,z2,z3,z4,z6,z343]),(0,[z1,z344,z7,z2,z3,z4,z6])],[(0,[z225,z1,z7,z2,z3,z4,z6]),(1,[z81,z1,z2,z123,z4,z6]),(0,[z345,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z4,z121,z6,z14])],[(1,[z164,z41,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z346,z6]),(0,[z1,z7,z2,z3,z347,z4,z6]),(0,[z1,z7,z2,z3,z4,z348,z6]),(1,[z1,z7,z2,z93,z4,z6]),(0,[z1,z7,z2,z3,z4,z349,z6])],[(0,[z1,z7,z13,z2,z16,z4,z6]),(0,[z49,z269,z1,z7,z2,z3,z6]),(0,[z35,z81,z1,z2,z3,z4,z6]),(0,[z1,z7,z2,z350,z3,z4,z6]),(0,[z351,z1,z7,z2,z3,z4,z6]),(0,[z136,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z4,z6,z14,z31])]],
   [[(0,[z88,z0,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z352,z6]),(0,[z1,z7,z11,z2,z240,z4,z6])],[(0,[z1,z7,z2,z3,z353,z4,z6]),(0,[z1,z7,z2,z228,z4,z79,z6]),(0,[z1,z7,z354,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z355,z6]),(0,[z49,z1,z7,z8,z2,z3,z6]),(0,[z1,z7,z2,z190,z3,z4,z6]),(0,[z332,z1,z7,z2,z16,z4,z6])],[(0,[z164,z7,z2,z3,z4,z6,z156]),(0,[z1,z7,z2,z3,z4,z356,z6]),(0,[z269,z7,z2,z3,z4,z79,z6]),(0,[z88,z1,z7,z2,z357,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z358]),(0,[z56,z1,z7,z2,z4,z6,z14])],[(0,[z87,z1,z7,z2,z3,z238,z6]),(1,[z49,z1,z7,z57,z3,z6]),(0,[z359,z1,z7,z2,z3,z4,z6]),(0,[z1,z360,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z4,z6,z31])],[(0,[z1,z7,z2,z3,z4,z361,z6])],[(0,[z1,z7,z2,z3,z362,z4,z6]),(0,[z1,z7,z2,z19,z4,z6,z14]),(0,[z88,z1,z7,z2,z4,z6,z14]),(0,[z7,z2,z3,z4,z89,z6,z156]),(0,[z1,z7,z2,z3,z4,z363,z6]),(1,[z7,z2,z3,z4,z6,z364]),(0,[z49,z49,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z3,z365,z4,z6]),(0,[z1,z7,z2,z16,z3,z4,z6]),(1,[z1,z7,z2,z3,z6,z113])],[(0,[z1,z7,z2,z3,z4,z6,z366]),(0,[z155,z1,z7,z11,z2,z3,z6]),(0,[z91,z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z4,z6,z367]),(1,[z315,z1,z2,z3,z30,z6]),(0,[z368,z1,z7,z2,z3,z4,z6]),(0,[z369,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z4,z162,z6]),(0,[z1,z7,z2,z3,z4,z370,z6])],[(0,[z1,z124,z42,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z139]),(0,[z1,z7,z11,z140,z2,z3,z6]),(0,[z371,z1,z7,z2,z3,z4,z6]),(0,[z173,z1,z7,z2,z3,z6,z31])]],
   [[(0,[z81,z1,z7,z2,z3,z4,z6]),(0,[z173,z1,z7,z2,z4,z6,z14])],[(0,[z1,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z372,z4,z6]),(0,[z1,z7,z2,z3,z373,z4,z6]),(0,[z374,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z375,z3,z4,z6]),(1,[z1,z239,z2,z3,z4,z6]),(0,[z88,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z376,z3,z4,z6]),(0,[z49,z1,z7,z2,z3,z129,z6]),(0,[z1,z7,z11,z2,z16,z3,z6]),(0,[z1,z7,z2,z3,z377,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z122]),(0,[z1,z7,z2,z378,z4,z52,z6])],[(0,[z1,z7,z2,z3,z379,z4,z6]),(0,[z1,z7,z2,z3,z380,z4,z6]),(0,[z1,z7,z2,z381,z3,z4,z6]),(0,[z1,z124,z7,z2,z3,z4,z25]),(0,[z49,z1,z7,z57,z2,z3,z6]),(0,[z49,z1,z7,z2,z3,z21,z6]),(0,[z1,z7,z8,z3,z4,z121,z6]),(0,[z85,z1,z7,z2,z16,z4,z6])],[(0,[z1,z7,z2,z16,z30,z4,z6]),(0,[z1,z7,z2,z3,z244,z4,z6]),(0,[z85,z1,z7,z2,z3,z4,z14]),(0,[z1,z7,z2,z4,z6,z275,z14]),(1,[z1,z7,z2,z4,z6,z53])],[(0,[z1,z7,z42,z11,z2,z3,z6]),(0,[z382,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z383]),(1,[z49,z1,z7,z3,z162,z6]),(0,[z173,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z16,z16,z4,z6]),(0,[z1,z7,z2,z3,z384,z4,z6])],[(0,[z1,z7,z2,z3,z204,z4,z6]),(1,[z232,z7,z2,z3,z19,z6]),(1,[z183,z7,z2,z3,z4,z6]),(0,[z385,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z4,z349,z6]),(0,[z1,z7,z386,z2,z3,z4,z6]),(0,[z173,z1,z7,z2,z3,z4,z31]),(0,[z1,z7,z2,z3,z4,z6,z387])],[(0,[z388,z1,z7,z2,z3,z4,z6]),(0,[z87,z1,z7,z2,z159,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z389]),(0,[z1,z7,z2,z3,z4,z4,z6]),(0,[z1,z7,z2,z3,z4,z89,z6]),(0,[z1,z7,z2,z3,z174,z129,z6]),(0,[z1,z390,z7,z2,z3,z4,z6])]],
   [[(0,[z41,z1,z7,z2,z3,z4,z6]),(0,[z391,z1,z7,z2,z3,z4,z6]),(0,[z81,z1,z7,z2,z16,z4,z6])],[(0,[z1,z7,z2,z392,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z393,z6]),(0,[z394,z1,z7,z2,z3,z4,z6]),(0,[z136,z1,z7,z2,z3,z4,z121])],[(0,[z49,z1,z7,z2,z3,z6,z25]),(0,[z1,z7,z2,z3,z4,z6,z395]),(0,[z396,z1,z7,z2,z3,z4,z6]),(0,[z49,z111,z1,z7,z2,z3,z6]),(1,[z1,z7,z11,z2,z240,z6]),(0,[z1,z7,z2,z4,z52,z6,z14]),(0,[z1,z7,z2,z3,z4,z6,z397])],[(0,[z398,z1,z7,z2,z3,z4,z6]),(0,[z111,z81,z1,z7,z2,z4,z6]),(0,[z1,z399,z7,z2,z3,z4,z6])],[(0,[z400,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z132,z3,z4,z6]),(0,[z1,z7,z2,z3,z30,z19,z6]),(0,[z1,z7,z2,z3,z401,z4,z6]),(0,[z402,z1,z7,z2,z3,z4,z6]),(0,[z403,z1,z7,z2,z3,z4,z6])],[(0,[z73,z7,z2,z3,z4,z6,z25]),(0,[z1,z124,z7,z2,z16,z4,z6]),(1,[z1,z7,z3,z134,z4,z6]),(0,[z1,z7,z2,z16,z21,z4,z6])],[(0,[z404,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z405,z4,z6]),(0,[z272,z1,z2,z3,z4,z6,z156]),(0,[z1,z7,z11,z2,z3,z69,z6]),(0,[z1,z7,z2,z3,z4,z406,z6]),(0,[z407,z1,z7,z2,z3,z4,z6])],[(0,[z408,z1,z7,z2,z3,z4,z6]),(0,[z409,z1,z7,z2,z3,z4,z6]),(0,[z54,z49,z1,z7,z3,z4,z6]),(0,[z111,z1,z7,z2,z3,z129,z6]),(0,[z82,z1,z7,z2,z3,z4,z5])]],
   [[(0,[z41,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z2,z3,z4,z43,z6]),(0,[z1,z7,z2,z3,z4,z6,z410]),(0,[z1,z7,z2,z4,z89,z6,z14]),(0,[z1,z64,z7,z3,z17,z4,z6]),(0,[z81,z1,z7,z2,z21,z4,z6]),(0,[z411,z1,z7,z2,z3,z4,z6]),(0,[z412,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z27])],[(0,[z1,z7,z9,z3,z4,z6,z27]),(0,[z1,z7,z2,z3,z4,z413,z6]),(0,[z88,z1,z7,z2,z414,z4,z6]),(0,[z49,z1,z7,z2,z67,z3,z6]),(0,[z1,z7,z2,z415,z3,z4,z6]),(0,[z1,z7,z11,z2,z3,z6,z31])],[(0,[z1,z7,z2,z3,z4,z6,z416]),(0,[z1,z7,z2,z3,z417,z4,z6]),(0,[z1,z7,z2,z4,z129,z6,z14]),(0,[z1,z7,z2,z128,z3,z52,z6]),(0,[z1,z7,z2,z418,z3,z4,z6])],[(0,[z49,z55,z1,z7,z2,z3,z6]),(0,[z419,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z20,z3,z83,z4,z6]),(0,[z1,z7,z11,z2,z3,z6,z110]),(0,[z223,z1,z7,z2,z16,z4,z6])],[(0,[z155,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z132,z16,z4,z6]),(0,[z1,z7,z11,z2,z3,z162,z6])],[(0,[z1,z7,z2,z3,z4,z6,z420]),(0,[z1,z7,z2,z16,z4,z6,z156]),(0,[z49,z1,z7,z2,z3,z6,z14]),(1,[z1,z7,z2,z3,z421,z6])],[(0,[z1,z7,z2,z3,z422,z4,z6]),(0,[z1,z7,z2,z3,z4,z423,z6])],[(0,[z82,z164,z1,z2,z3,z4,z6]),(0,[z1,z7,z424,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z3,z159,z6]),(0,[z1,z7,z2,z16,z4,z89,z6]),(0,[z63,z1,z7,z140,z3,z4,z6]),(0,[z82,z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z11,z11,z2,z3,z6]),(1,[z1,z7,z2,z240,z4,z6])]],
   [[(0,[z1,z7,z2,z425,z3,z4,z6]),(0,[z87,z1,z7,z2,z132,z4,z6]),(0,[z1,z7,z181,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z295,z6]),(0,[z1,z7,z8,z3,z17,z4,z6]),(0,[z411,z1,z7,z2,z16,z4,z6])],[(0,[z1,z7,z2,z4,z89,z6,z426]),(0,[z427,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z67,z3,z4,z6,z27]),(0,[z428,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z174,z4,z52])],[(0,[z1,z7,z2,z429,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z430,z6]),(0,[z431,z1,z7,z11,z2,z3,z6])],[(0,[z1,z7,z2,z432,z3,z4,z6]),(0,[z1,z7,z2,z433,z3,z4,z6]),(0,[z1,z7,z2,z3,z434,z4,z6]),(0,[z49,z1,z7,z3,z83,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z435]),(1,[z50,z1,z7,z2,z6,z14])],[(0,[z55,z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z436,z3,z4,z6]),(0,[z1,z7,z2,z3,z437,z4,z6]),(1,[z1,z7,z2,z3,z304,z6]),(0,[z88,z7,z2,z3,z4,z6,z156]),(0,[z49,z1,z7,z11,z3,z4,z6])],[(0,[z88,z1,z7,z2,z3,z4,z156]),(1,[z63,z1,z67,z3,z4,z6]),(0,[z1,z7,z2,z67,z3,z4,z6]),(0,[z438,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z439,z6]),(0,[z315,z1,z2,z3,z30,z4,z6]),(0,[z1,z7,z2,z20,z3,z84,z6]),(0,[z49,z1,z7,z2,z261,z3,z6]),(0,[z136,z1,z7,z2,z3,z4,z27]),(0,[z1,z7,z2,z3,z421,z4,z6]),(0,[z1,z7,z2,z128,z4,z6,z14])],[(0,[z440,z1,z7,z2,z3,z4,z6]),(0,[z91,z1,z7,z2,z3,z4,z156]),(0,[z1,z64,z7,z2,z4,z6,z14]),(1,[z1,z7,z2,z4,z6,z148]),(0,[z441,z1,z7,z11,z2,z3,z6])],[(0,[z442,z1,z7,z2,z3,z4,z6]),(0,[z1,z443,z7,z2,z3,z4,z6]),(0,[z444,z1,z7,z2,z3,z4,z6]),(0,[z445,z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z4,z6,z53])]],
   [[(0,[z0,z1,z7,z2,z4,z6,z14]),(0,[z164,z91,z7,z2,z3,z4,z6]),(0,[z446,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z447]),(1,[z1,z7,z2,z3,z448,z6]),(0,[z1,z7,z2,z16,z4,z6,z27]),(0,[z111,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z317])],[(0,[z1,z7,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z449,z3,z4,z6]),(0,[z55,z1,z7,z11,z2,z3,z6]),(0,[z155,z7,z2,z3,z159,z4,z6]),(1,[z1,z7,z2,z329,z4,z6])],[(0,[z41,z7,z42,z2,z3,z4,z6]),(0,[z450,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z451,z2,z3,z4,z6]),(0,[z1,z7,z2,z452,z3,z4,z6]),(0,[z1,z7,z2,z453,z3,z4,z6])],[(0,[z454,z1,z7,z2,z3,z4,z6]),(0,[z455,z1,z7,z2,z3,z4,z6])],[(0,[z1,z456,z7,z2,z3,z4,z6]),(0,[z155,z1,z7,z2,z21,z4,z6]),(0,[z269,z1,z7,z11,z2,z3,z6]),(0,[z232,z1,z7,z11,z2,z3,z6]),(0,[z88,z1,z7,z2,z3,z247,z6]),(0,[z1,z7,z2,z457,z3,z4,z6]),(1,[z458,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z3,z4,z6,z459]),(0,[z1,z7,z2,z20,z4,z6,z14]),(0,[z351,z49,z1,z7,z2,z3,z6]),(0,[z460,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z461,z3,z4,z6]),(0,[z218,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z462,z2,z3,z4,z6]),(0,[z55,z7,z13,z2,z3,z4,z6]),(0,[z1,z7,z463,z2,z3,z4,z6]),(1,[z1,z7,z2,z109,z4,z6]),(0,[z1,z7,z2,z67,z16,z4,z6]),(0,[z1,z464,z7,z11,z2,z3,z6]),(0,[z1,z7,z465,z2,z3,z4,z6])],[(0,[z1,z7,z466,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z467,z4,z6]),(0,[z468,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z174,z4,z6,z14])],[(0,[z1,z7,z2,z3,z4,z6,z469]),(0,[z54,z1,z7,z11,z2,z3,z6]),(1,[z1,z171,z2,z3,z4,z6]),(1,[z49,z1,z7,z3,z6,z27])]],
   [[(0,[z470,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z471,z4,z6]),(0,[z41,z1,z2,z3,z4,z6,z25]),(1,[z225,z1,z7,z2,z4,z6]),(0,[z35,z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z472,z4,z6]),(0,[z1,z7,z2,z3,z448,z4,z6]),(0,[z111,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z2,z3,z4,z473,z6]),(0,[z1,z7,z2,z3,z474,z4,z6]),(0,[z1,z7,z2,z4,z6,z14,z274]),(0,[z1,z7,z2,z16,z174,z4,z6])],[(0,[z1,z7,z2,z475,z3,z4,z6]),(0,[z1,z7,z2,z3,z476,z4,z6]),(0,[z1,z7,z2,z477,z3,z4,z6]),(0,[z478,z1,z7,z2,z3,z4,z6]),(0,[z56,z1,z7,z2,z83,z4,z6]),(0,[z1,z7,z57,z2,z83,z4,z6]),(0,[z1,z7,z2,z3,z4,z479,z6]),(0,[z1,z7,z2,z128,z3,z62,z6])],[(0,[z1,z7,z11,z2,z3,z79,z6]),(0,[z272,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z294,z3,z4,z6]),(0,[z458,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z3,z84,z6]),(0,[z136,z1,z7,z2,z126,z4,z6]),(0,[z1,z7,z2,z453,z16,z4,z6]),(0,[z1,z7,z2,z3,z4,z480,z6]),(1,[z1,z7,z3,z4,z6,z158])],[(0,[z49,z1,z7,z2,z3,z19,z6]),(0,[z1,z7,z11,z2,z3,z6,z156]),(0,[z49,z1,z7,z2,z3,z30,z6]),(1,[z82,z1,z2,z3,z4,z25]),(0,[z1,z7,z2,z3,z4,z481,z6]),(0,[z49,z1,z7,z2,z2,z3,z6]),(0,[z49,z1,z7,z2,z3,z174,z6]),(0,[z1,z7,z2,z3,z121,z6,z303]),(0,[z1,z7,z482,z2,z3,z4,z6])],[(0,[z76,z1,z7,z2,z9,z4,z6]),(0,[z70,z1,z7,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z6,z364,z25]),(0,[z483,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z11,z2,z3,z89,z6]),(0,[z35,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z3,z4,z484,z6])],[(0,[z49,z1,z7,z13,z2,z3,z6]),(0,[z1,z7,z2,z485,z3,z4,z6]),(0,[z486,z1,z7,z2,z3,z4,z6]),(1,[z173,z1,z7,z2,z3,z31]),(1,[z1,z7,z2,z3,z174,z52])],[(0,[z1,z7,z2,z487,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z488,z6]),(0,[z35,z1,z7,z57,z2,z4,z6]),(0,[z82,z183,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z3,z6,z489]),(0,[z490,z1,z7,z2,z3,z4,z6])]],
   [[(0,[z1,z7,z2,z2,z3,z4,z6]),(0,[z431,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z491,z4,z6])],[(0,[z492,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z493,z4,z6]),(0,[z494,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z495,z4,z6]),(1,[z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z4,z496,z6])],[(0,[z1,z7,z2,z497,z3,z4,z6]),(0,[z1,z7,z2,z16,z69,z4,z6]),(0,[z1,z7,z2,z498,z3,z4,z6]),(0,[z499,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z302,z3,z4,z6])],[(0,[z1,z7,z2,z3,z19,z6,z31]),(0,[z1,z7,z2,z3,z4,z6,z500]),(0,[z501,z1,z7,z2,z3,z4,z6]),(0,[z49,z1,z64,z7,z3,z4,z6]),(0,[z49,z1,z7,z2,z3,z12,z6])],[(0,[z63,z1,z7,z3,z17,z4,z6]),(0,[z1,z2,z3,z30,z4,z129,z6]),(0,[z315,z49,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z83,z4,z6,z14])],[(0,[z1,z7,z2,z502,z3,z4,z6]),(0,[z0,z1,z7,z2,z3,z224,z6]),(0,[z1,z7,z503,z2,z3,z4,z6]),(0,[z54,z7,z2,z9,z3,z4,z6]),(0,[z1,z7,z2,z128,z3,z79,z6]),(0,[z1,z7,z140,z2,z16,z4,z6]),(0,[z81,z1,z7,z2,z69,z4,z6]),(0,[z1,z7,z2,z3,z448,z83,z6]),(0,[z49,z1,z7,z2,z3,z121,z6]),(0,[z22,z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z4,z6,z504])],[(1,[z1,z114,z7,z2,z3,z6]),(1,[z269,z7,z2,z3,z79,z6]),(0,[z1,z7,z2,z109,z3,z4,z6]),(0,[z505,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z506,z6]),(0,[z1,z7,z2,z3,z119,z4,z6]),(1,[z49,z1,z7,z11,z3,z6]),(0,[z1,z7,z11,z2,z3,z6,z27])],[(0,[z1,z7,z2,z507,z3,z4,z6]),(0,[z1,z7,z2,z3,z508,z4,z6]),(0,[z509,z1,z7,z2,z3,z4,z6]),(0,[z232,z1,z7,z2,z3,z79,z6]),(0,[z1,z7,z2,z3,z4,z6,z510]),(0,[z511,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z378,z4,z6])]],
   [[(0,[z512,z1,z7,z2,z3,z4,z6]),(0,[z35,z1,z7,z2,z123,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z513]),(0,[z1,z7,z2,z3,z277,z4,z6]),(0,[z111,z1,z7,z2,z3,z30,z6]),(0,[z1,z7,z2,z3,z514,z4,z6]),(0,[z515,z1,z7,z2,z3,z4,z6])],[(0,[z164,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z290,z2,z3,z4,z6]),(0,[z1,z239,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z516,z3,z4,z6]),(0,[z1,z2,z123,z3,z69,z4,z6]),(0,[z315,z1,z7,z2,z3,z129,z6]),(0,[z1,z7,z2,z3,z4,z129,z6]),(0,[z1,z7,z2,z3,z4,z6,z148]),(0,[z1,z7,z11,z2,z20,z3,z6]),(0,[z1,z7,z2,z3,z4,z6,z517])],[(0,[z1,z7,z518,z2,z3,z4,z6]),(0,[z460,z1,z7,z2,z3,z4,z6]),(0,[z55,z1,z7,z13,z3,z4,z6]),(1,[z87,z7,z2,z132,z4,z6]),(1,[z1,z7,z2,z4,z6,z426]),(0,[z519,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z71,z4,z6]),(0,[z136,z49,z1,z7,z2,z3,z6])],[(0,[z1,z7,z520,z2,z3,z4,z6]),(0,[z521,z1,z7,z2,z3,z4,z6]),(0,[z1,z117,z7,z2,z3,z129,z6]),(0,[z1,z7,z195,z2,z3,z4,z6]),(0,[z1,z522,z7,z2,z3,z4,z6]),(0,[z50,z1,z7,z2,z4,z6,z14])],[(0,[z1,z7,z2,z9,z3,z4,z6]),(0,[z523,z1,z7,z2,z3,z4,z6]),(0,[z82,z1,z7,z350,z3,z4,z6]),(0,[z1,z7,z2,z4,z6,z6,z14]),(0,[z1,z7,z2,z3,z329,z4,z6])],[(0,[z1,z7,z2,z3,z4,z524,z6]),(0,[z54,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z525,z6]),(0,[z1,z7,z57,z2,z4,z6,z14])],[(0,[z56,z87,z1,z7,z2,z4,z6]),(0,[z526,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z527,z3,z4,z6])],[(0,[z528,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z529]),(0,[z1,z7,z2,z3,z4,z530,z6]),(0,[z1,z7,z11,z2,z415,z3,z6]),(0,[z1,z7,z2,z3,z4,z6,z531])]],
   [[(0,[z1,z7,z2,z3,z4,z532,z6]),(0,[z54,z1,z7,z13,z3,z4,z6]),(0,[z49,z87,z1,z7,z2,z3,z6]),(0,[z533,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z4,z6,z14,z331]),(0,[z515,z1,z7,z2,z16,z4,z6])],[(0,[z164,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z2,z169,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z534,z6]),(0,[z1,z7,z2,z3,z4,z6,z25]),(0,[z1,z535,z7,z2,z3,z4,z6]),(0,[z1,z7,z536,z2,z3,z4,z6])],[(0,[z0,z1,z7,z2,z3,z537,z6]),(0,[z88,z91,z7,z2,z3,z4,z6]),(0,[z56,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z3,z4,z538,z6]),(0,[z1,z7,z539,z2,z3,z4,z6])],[(0,[z55,z1,z7,z9,z3,z4,z6]),(0,[z540,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z80,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z6]),(0,[z1,z7,z2,z16,z4,z5,z6]),(0,[z1,z7,z3,z17,z4,z162,z6]),(0,[z1,z7,z2,z4,z6,z113,z14])],[(0,[z1,z7,z2,z9,z16,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z541]),(0,[z1,z7,z2,z294,z4,z89,z6]),(0,[z1,z64,z7,z2,z3,z243,z6]),(0,[z35,z1,z2,z3,z69,z4,z6]),(0,[z1,z542,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z3,z17,z6]),(0,[z1,z7,z2,z4,z12,z6,z14])],[(0,[z87,z1,z7,z2,z4,z6,z14]),(0,[z543,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z414,z4,z6])],[(1,[z1,z7,z2,z3,z224,z6]),(0,[z54,z55,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z544]),(0,[z91,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z545,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z32]),(0,[z1,z7,z2,z3,z4,z546,z6]),(0,[z1,z7,z2,z527,z16,z4,z6]),(0,[z1,z7,z2,z3,z547,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z548])],[(0,[z49,z1,z117,z7,z2,z3,z6])]],
   [[(0,[z82,z0,z1,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z549]),(0,[z550,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z551,z4,z6]),(1,[z1,z7,z552,z3,z4,z6]),(0,[z173,z49,z1,z7,z2,z3,z6])],[(0,[z54,z1,z7,z9,z3,z4,z6]),(0,[z1,z7,z2,z553,z3,z4,z6]),(0,[z1,z7,z2,z16,z4,z129,z6]),(0,[z1,z7,z2,z16,z3,z4,z14]),(1,[z1,z7,z2,z16,z4,z12])],[(0,[z554,z1,z7,z2,z3,z4,z6]),(0,[z87,z1,z7,z11,z2,z3,z6]),(0,[z555,z1,z7,z2,z3,z4,z6]),(0,[z1,z556,z7,z2,z3,z4,z6]),(0,[z315,z1,z7,z2,z3,z4,z6]),(0,[z202,z1,z7,z2,z3,z4,z6]),(0,[z438,z49,z1,z7,z2,z3,z6]),(0,[z1,z7,z557,z2,z3,z4,z6])],[(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z558,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z559,z11,z2,z3,z6]),(0,[z1,z7,z2,z474,z4,z6,z14])],[(0,[z7,z13,z2,z9,z3,z4,z6]),(0,[z1,z7,z2,z3,z560,z4,z6]),(0,[z87,z1,z7,z57,z2,z4,z6]),(0,[z1,z7,z2,z3,z561,z4,z6]),(0,[z1,z117,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z562]),(0,[z49,z1,z7,z2,z3,z340,z6]),(0,[z563,z1,z7,z2,z3,z4,z6]),(0,[z112,z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z4,z6,z14])],[(0,[z1,z7,z564,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z184,z6]),(0,[z1,z7,z2,z3,z4,z6,z565])],[(0,[z1,z7,z2,z3,z4,z566,z6]),(1,[z1,z7,z133,z2,z3,z6]),(0,[z1,z7,z567,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z568,z6]),(1,[z1,z7,z2,z58,z4,z6])],[(0,[z49,z1,z7,z2,z123,z3,z6]),(0,[z1,z7,z2,z3,z30,z174,z6]),(1,[z1,z7,z11,z3,z17,z6])]],
   [[(0,[z55,z1,z7,z2,z3,z101,z6]),(0,[z1,z7,z2,z3,z210,z4,z6]),(0,[z569,z1,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z128,z3,z6]),(0,[z136,z1,z7,z2,z3,z4,z6]),(0,[z570,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z3,z159,z4,z6]),(0,[z1,z7,z2,z3,z304,z4,z6]),(0,[z1,z7,z571,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z572,z6]),(0,[z1,z7,z2,z378,z3,z4,z6])],[(0,[z315,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z573,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z574]),(0,[z575,z1,z7,z2,z3,z4,z6])],[(1,[z1,z7,z2,z3,z537,z6]),(0,[z49,z41,z1,z7,z2,z3,z6]),(0,[z1,z114,z7,z2,z3,z4,z6]),(0,[z202,z1,z7,z3,z4,z129,z6]),(0,[z468,z49,z1,z7,z2,z3,z6]),(0,[z111,z1,z7,z2,z3,z21,z6]),(0,[z1,z7,z2,z16,z4,z6,z6])],[(0,[z576,z1,z7,z2,z3,z4,z6]),(0,[z259,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z3,z210,z6]),(0,[z1,z117,z7,z2,z16,z4,z6])],[(0,[z1,z7,z2,z3,z4,z6,z426]),(0,[z577,z1,z7,z2,z3,z4,z6]),(0,[z578,z1,z7,z2,z3,z4,z6]),(0,[z173,z111,z1,z7,z2,z3,z6])],[(1,[z1,z7,z350,z3,z4,z6]),(0,[z1,z7,z2,z579,z3,z4,z6]),(0,[z1,z7,z2,z16,z547,z4,z6]),(0,[z1,z7,z2,z192,z3,z4,z6])],[(1,[z1,z7,z2,z3,z243,z6]),(0,[z1,z7,z2,z3,z4,z6,z580])]],
   [[(1,[z1,z7,z2,z3,z247,z6]),(1,[z391,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z3,z4,z581,z6]),(0,[z136,z1,z7,z2,z16,z4,z6]),(0,[z75,z1,z7,z2,z4,z6,z14])],[(0,[z582,z1,z7,z2,z3,z4,z6]),(0,[z583,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z584,z4,z6]),(0,[z1,z7,z2,z3,z585,z4,z6]),(0,[z82,z1,z7,z2,z381,z4,z6]),(0,[z1,z7,z11,z2,z3,z5,z6]),(0,[z1,z7,z2,z586,z3,z4,z6]),(1,[z1,z7,z8,z3,z4,z121])],[(0,[z1,z7,z2,z277,z4,z129,z6]),(0,[z1,z7,z2,z3,z587,z4,z6]),(0,[z85,z1,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z130,z4,z6])],[(0,[z588,z1,z7,z2,z3,z4,z6]),(0,[z88,z1,z7,z2,z3,z4,z6])],[(0,[z589,z1,z7,z2,z3,z4,z6]),(0,[z91,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z590,z6]),(0,[z1,z124,z7,z2,z3,z4,z5]),(0,[z1,z7,z2,z3,z4,z6,z241])],[(0,[z1,z7,z2,z3,z4,z6,z591]),(0,[z1,z7,z2,z3,z592,z4,z6]),(0,[z1,z7,z66,z2,z3,z4,z6]),(0,[z1,z7,z2,z593,z3,z4,z6]),(0,[z75,z1,z7,z11,z2,z3,z6])],[(0,[z1,z7,z42,z2,z3,z4,z6]),(0,[z594,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z303]),(0,[z173,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z595,z6])],[(0,[z155,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z2,z4,z6,z156,z14]),(0,[z1,z596,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z140,z2,z3,z6]),(0,[z1,z7,z11,z2,z3,z129,z6]),(0,[z82,z1,z7,z11,z2,z3,z6]),(0,[z111,z1,z7,z2,z20,z4,z6]),(0,[z1,z7,z597,z2,z3,z4,z6]),(0,[z1,z7,z2,z4,z6,z14,z410]),(0,[z173,z1,z7,z2,z3,z4,z52])]],
   [[(0,[z1,z7,z2,z3,z4,z6,z598]),(0,[z1,z7,z2,z3,z4,z599,z6]),(0,[z1,z7,z552,z2,z3,z4,z6]),(1,[z50,z1,z7,z2,z3,z6])],[(0,[z1,z7,z2,z16,z159,z4,z6]),(1,[z1,z7,z2,z3,z271,z6]),(0,[z1,z7,z559,z2,z3,z4,z6])],[(0,[z600,z1,z7,z2,z3,z4,z6]),(0,[z88,z1,z7,z34,z3,z4,z6]),(0,[z91,z7,z2,z3,z4,z89,z6]),(1,[z35,z1,z2,z69,z4,z6]),(0,[z315,z1,z7,z2,z3,z30,z6]),(0,[z1,z7,z2,z3,z601,z4,z6])],[(0,[z88,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z602,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z603,z4,z6]),(0,[z604,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z605])],[(0,[z91,z1,z7,z2,z16,z4,z6]),(0,[z1,z117,z7,z2,z3,z30,z6]),(0,[z1,z117,z2,z3,z4,z129,z6]),(0,[z1,z124,z7,z2,z4,z6,z14]),(0,[z1,z7,z37,z2,z3,z4,z6])],[(0,[z606,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z3,z204,z4,z6]),(0,[z1,z7,z2,z3,z79,z6,z31]),(0,[z607,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z3,z17,z4,z6,z27])],[(0,[z1,z7,z42,z2,z16,z4,z6]),(0,[z608,z1,z7,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z139,z156]),(0,[z1,z64,z7,z11,z2,z3,z6]),(0,[z81,z1,z2,z123,z3,z4,z6]),(0,[z1,z199,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z489]),(1,[z1,z7,z11,z2,z58,z6]),(0,[z173,z1,z7,z2,z16,z4,z6])],[(0,[z41,z1,z7,z2,z4,z6,z14]),(0,[z609,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z610]),(0,[z232,z49,z1,z7,z2,z3,z6]),(0,[z49,z1,z7,z2,z3,z52,z6]),(0,[z611,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z3,z612,z4,z6])]],
   [[(0,[z0,z1,z7,z11,z2,z3,z6]),(1,[z1,z7,z2,z3,z273,z6]),(0,[z1,z7,z2,z613,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z614,z6]),(0,[z394,z1,z7,z2,z4,z6,z14])],[(1,[z0,z42,z2,z3,z4,z6]),(0,[z1,z7,z2,z615,z3,z4,z6]),(0,[z1,z64,z7,z67,z3,z4,z6]),(0,[z1,z7,z2,z3,z616,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z617]),(0,[z1,z7,z2,z3,z618,z4,z6]),(0,[z1,z7,z8,z2,z4,z6,z14])],[(0,[z54,z49,z1,z7,z2,z3,z6]),(0,[z232,z269,z7,z2,z3,z4,z6]),(0,[z85,z1,z7,z2,z3,z4,z12]),(0,[z1,z7,z2,z3,z4,z12,z6])],[(0,[z1,z7,z2,z619,z3,z4,z6]),(0,[z87,z7,z2,z132,z3,z4,z6]),(0,[z1,z7,z2,z620,z3,z4,z6]),(0,[z1,z7,z2,z3,z30,z79,z6]),(0,[z1,z7,z2,z3,z4,z6,z621]),(0,[z1,z622,z7,z2,z3,z4,z6])],[(0,[z623,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z624,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z121,z6]),(0,[z625,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z3,z4,z12]),(0,[z1,z7,z2,z3,z174,z52,z6])],[(0,[z1,z7,z2,z3,z4,z626,z6]),(0,[z627,z1,z7,z2,z3,z4,z6]),(0,[z82,z1,z124,z2,z3,z4,z6]),(0,[z1,z628,z7,z2,z3,z4,z6])],[(0,[z88,z1,z7,z80,z3,z4,z6]),(1,[z1,z7,z3,z182,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z629]),(1,[z49,z1,z7,z3,z83,z6])],[(0,[z630,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z11,z2,z132,z3,z6]),(0,[z1,z7,z2,z3,z631,z4,z6]),(0,[z1,z7,z2,z3,z632,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z364])]],
   [[(0,[z56,z35,z1,z7,z2,z4,z6]),(0,[z633,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z11,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z634,z4,z6])],[(1,[z1,z7,z2,z357,z4,z6]),(0,[z1,z7,z2,z3,z4,z635,z6]),(0,[z82,z1,z7,z552,z3,z4,z6]),(0,[z49,z1,z443,z7,z2,z3,z6]),(0,[z49,z1,z7,z2,z3,z6,z31]),(0,[z1,z7,z230,z11,z2,z3,z6]),(0,[z136,z1,z7,z2,z142,z4,z6])],[(0,[z63,z49,z1,z7,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z636]),(0,[z49,z35,z1,z7,z2,z3,z6]),(0,[z49,z1,z7,z2,z4,z6,z14]),(0,[z1,z637,z7,z2,z3,z4,z6]),(0,[z638,z1,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z3,z4,z639,z6]),(1,[z1,z7,z2,z381,z4,z6]),(0,[z56,z1,z7,z57,z3,z4,z6])],[(0,[z1,z7,z11,z2,z3,z159,z6]),(0,[z1,z7,z640,z2,z3,z4,z6]),(0,[z1,z7,z2,z641,z3,z4,z6]),(0,[z1,z7,z2,z17,z4,z6,z14]),(0,[z111,z1,z7,z2,z3,z52,z6]),(0,[z1,z7,z2,z3,z4,z6,z642])],[(0,[z1,z7,z2,z3,z4,z643,z6]),(0,[z49,z55,z1,z7,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z644,z6]),(0,[z87,z1,z7,z2,z3,z271,z6]),(1,[z49,z1,z7,z8,z3,z6]),(0,[z1,z7,z2,z3,z240,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z113]),(0,[z1,z7,z2,z3,z645,z4,z6])],[(0,[z164,z1,z42,z2,z3,z4,z6]),(0,[z91,z7,z42,z2,z3,z4,z6]),(0,[z49,z164,z1,z7,z2,z3,z6]),(0,[z7,z2,z132,z3,z159,z4,z6]),(0,[z1,z7,z646,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z647]),(0,[z1,z64,z7,z2,z3,z135,z6]),(1,[z1,z7,z2,z3,z6,z180]),(0,[z1,z648,z7,z2,z3,z4,z6])],[(0,[z649,z1,z7,z2,z3,z4,z6]),(1,[z49,z1,z7,z2,z6,z14]),(0,[z1,z7,z248,z11,z2,z3,z6]),(0,[z441,z1,z7,z2,z3,z4,z6])]],
   [[(0,[z155,z1,z7,z2,z159,z4,z6]),(0,[z650,z1,z7,z2,z3,z4,z6]),(0,[z70,z1,z7,z2,z4,z129,z6]),(0,[z1,z7,z11,z2,z16,z4,z6]),(0,[z1,z7,z2,z190,z4,z121,z6]),(0,[z651,z1,z7,z2,z3,z4,z6]),(0,[z1,z652,z7,z2,z3,z4,z6])],[(1,[z49,z55,z1,z7,z3,z6]),(0,[z1,z653,z7,z2,z3,z4,z6]),(1,[z1,z7,z11,z2,z3,z6]),(0,[z563,z49,z1,z7,z2,z3,z6])],[(0,[z1,z7,z2,z3,z654,z4,z6]),(0,[z55,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z13,z8,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z655,z6]),(0,[z1,z7,z656,z2,z3,z4,z6]),(0,[z657,z1,z7,z2,z3,z4,z6]),(0,[z315,z1,z117,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z658,z6]),(0,[z458,z1,z7,z2,z3,z83,z6]),(0,[z1,z7,z2,z16,z4,z12,z6])],[(0,[z1,z7,z659,z2,z3,z4,z6]),(0,[z111,z1,z7,z2,z3,z19,z6]),(0,[z660,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z83,z4,z6]),(0,[z1,z7,z2,z128,z3,z4,z6])],[(0,[z1,z64,z7,z2,z3,z4,z6]),(0,[z391,z1,z7,z2,z67,z4,z6]),(0,[z1,z7,z2,z67,z4,z6,z14]),(0,[z661,z1,z7,z2,z3,z4,z6])],[(0,[z269,z1,z7,z2,z3,z4,z6]),(0,[z232,z1,z7,z2,z3,z4,z6]),(0,[z1,z662,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z414,z3,z4,z6]),(1,[z1,z64,z140,z3,z4,z6]),(0,[z1,z7,z11,z2,z3,z83,z6]),(0,[z611,z1,z7,z2,z3,z4,z6]),(0,[z445,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z174,z4,z31])],[(0,[z0,z1,z7,z2,z3,z4,z6]),(0,[z663,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z664,z4,z6]),(0,[z49,z1,z7,z2,z3,z62,z6]),(0,[z1,z464,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z665,z4,z6]),(0,[z1,z7,z2,z666,z3,z4,z6])],[(0,[z667,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z668,z4,z6]),(0,[z111,z1,z7,z2,z4,z6,z14])]],
   [[(0,[z669,z1,z7,z2,z3,z4,z6]),(0,[z670,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z671,z3,z4,z6]),(0,[z672,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z128,z3,z134,z4,z6]),(1,[z1,z7,z265,z3,z4,z6])],[(0,[z155,z111,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z3,z673,z4,z6]),(0,[z1,z7,z2,z3,z17,z4,z6]),(1,[z136,z1,z7,z3,z4,z27]),(0,[z1,z7,z674,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z675])],[(0,[z164,z41,z7,z2,z3,z4,z6]),(0,[z1,z7,z276,z2,z3,z4,z6]),(0,[z55,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z2,z676,z3,z4,z6]),(0,[z1,z7,z2,z3,z421,z121,z6])],[(0,[z49,z1,z7,z42,z2,z3,z6]),(0,[z55,z1,z7,z2,z3,z43,z6]),(0,[z1,z7,z677,z2,z3,z4,z6]),(0,[z141,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z128,z16,z4,z6])],[(0,[z678,z1,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z89,z6]),(0,[z1,z7,z679,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z680,z6]),(0,[z1,z7,z2,z3,z4,z681,z6])],[(0,[z1,z7,z11,z2,z9,z3,z6]),(0,[z269,z1,z7,z2,z16,z4,z6]),(0,[z232,z1,z7,z2,z16,z4,z6]),(0,[z63,z1,z7,z2,z4,z6,z14]),(0,[z56,z49,z1,z7,z2,z3,z6]),(0,[z49,z369,z1,z7,z2,z3,z6]),(0,[z682,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z6,z683])],[(0,[z35,z1,z7,z2,z3,z4,z6]),(0,[z56,z81,z1,z7,z2,z4,z6]),(0,[z684,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z685,z6]),(0,[z1,z7,z2,z3,z686,z4,z6]),(0,[z1,z7,z2,z3,z687,z4,z6])],[(0,[z1,z7,z2,z688,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z689,z6]),(0,[z1,z7,z2,z123,z3,z4,z6]),(0,[z1,z7,z2,z3,z690,z4,z6]),(0,[z667,z1,z7,z2,z16,z4,z6])]],
   [[(0,[z1,z7,z2,z3,z4,z537,z6]),(0,[z54,z1,z7,z2,z16,z4,z6]),(0,[z88,z49,z1,z7,z2,z3,z6]),(0,[z1,z64,z140,z2,z3,z4,z6]),(0,[z49,z81,z1,z7,z2,z3,z6]),(0,[z1,z7,z11,z2,z3,z30,z6])],[(0,[z155,z1,z7,z2,z132,z4,z6]),(0,[z691,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z3,z135,z6]),(0,[z1,z7,z2,z692,z3,z4,z6]),(0,[z693,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z674,z2,z16,z4,z6])],[(0,[z49,z1,z7,z2,z3,z79,z6]),(0,[z63,z1,z7,z11,z2,z3,z6]),(0,[z1,z7,z2,z3,z4,z6,z694]),(0,[z1,z7,z695,z2,z3,z4,z6]),(0,[z1,z7,z265,z2,z3,z4,z6])],[(0,[z696,z1,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z3,z6,z156]),(0,[z1,z7,z2,z3,z697,z4,z6]),(0,[z698,z1,z7,z2,z3,z4,z6]),(0,[z499,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z83,z4,z6]),(0,[z111,z1,z7,z2,z3,z62,z6]),(0,[z1,z7,z2,z128,z21,z4,z6])],[(0,[z1,z7,z13,z3,z4,z6,z27]),(0,[z1,z7,z2,z28,z3,z4,z6]),(0,[z1,z7,z2,z3,z357,z4,z6]),(0,[z1,z7,z140,z2,z4,z6,z14])],[(0,[z155,z87,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z699,z6]),(0,[z63,z1,z7,z67,z3,z4,z6]),(0,[z700,z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z4,z701,z6])],[(0,[z702,z1,z7,z2,z3,z4,z6]),(0,[z35,z1,z7,z2,z16,z4,z6]),(0,[z1,z7,z2,z3,z4,z703,z6]),(0,[z49,z1,z7,z3,z4,z162,z6])],[(1,[z1,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z704,z3,z4,z6]),(0,[z1,z7,z2,z3,z174,z79,z6]),(0,[z1,z7,z2,z3,z4,z705,z6]),(0,[z1,z7,z2,z123,z16,z4,z6]),(0,[z706,z1,z7,z2,z3,z4,z6]),(1,[z1,z7,z2,z6,z113,z14]),(0,[z1,z7,z37,z3,z4,z52,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z42,z2,z3,z4,z6]),(0,[z48,z7,z2,z3,z19,z6]),(0,[z1,z7,z2,z126,z4,z6]),(0,[z1,z7,z2,z58,z240,z6])],[(0,[z707,z1,z7,z2,z3,z6]),(0,[z1,z7,z11,z2,z708,z6]),(0,[z50,z22,z1,z7,z2,z6])],[(0,[z1,z7,z2,z3,z709,z6])],[(0,[z710,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z711,z4,z6]),(0,[z269,z199,z7,z2,z3,z6])],[(0,[z1,z7,z2,z16,z101,z6]),(0,[z1,z7,z712,z34,z3,z6]),(0,[z49,z1,z2,z3,z6,z139]),(0,[z1,z7,z713,z3,z4,z6]),(0,[z1,z7,z350,z244,z4,z6])],[(0,[z714,z1,z7,z2,z3,z6]),(0,[z49,z1,z7,z2,z357,z6]),(0,[z1,z7,z2,z715,z4,z6]),(0,[z1,z146,z2,z3,z129,z6]),(1,[z1,z2,z3,z4,z716])],[(0,[z49,z259,z1,z7,z3,z6]),(0,[z49,z267,z1,z7,z3,z6]),(0,[z1,z7,z265,z3,z129,z6]),(0,[z198,z49,z1,z7,z83,z6])],[(0,[z54,z49,z199,z7,z3,z6]),(0,[z1,z7,z2,z717,z4,z6]),(0,[z225,z1,z7,z204,z4,z6]),(0,[z1,z7,z3,z4,z6,z718]),(0,[z1,z7,z3,z719,z4,z6]),(0,[z50,z1,z7,z2,z20,z6]),(0,[z1,z7,z720,z3,z6,z113])],[(0,[z0,z42,z2,z16,z4,z6]),(0,[z49,z1,z721,z7,z3,z6])],[],[(0,[z1,z7,z2,z722,z4,z6]),(0,[z88,z7,z2,z3,z4,z156]),(0,[z723,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z381,z4,z6]),(0,[z1,z7,z11,z2,z381,z6]),(0,[z49,z1,z7,z57,z6,z14]),(0,[z49,z1,z7,z597,z3,z6]),(0,[z173,z1,z7,z2,z58,z6])],[(0,[z220,z1,z7,z2,z4,z14]),(0,[z98,z49,z1,z7,z3,z6])],[(0,[z1,z7,z2,z724,z4,z6]),(0,[z1,z7,z133,z2,z16,z6]),(0,[z49,z1,z7,z8,z3,z6]),(0,[z1,z7,z2,z128,z21,z6])],[(0,[z88,z7,z2,z4,z156,z14]),(0,[z1,z7,z2,z3,z6,z180]),(0,[z1,z7,z2,z3,z6,z725])],[(0,[z81,z1,z2,z123,z210,z6]),(0,[z1,z7,z57,z3,z71,z6]),(0,[z726,z1,z7,z2,z16,z6])],[(0,[z1,z7,z2,z727,z4,z6]),(0,[z1,z728,z2,z3,z4,z6])]],
   [[(0,[z49,z55,z1,z7,z3,z6]),(0,[z729,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z730,z6]),(0,[z1,z140,z713,z3,z4,z6])],[(0,[z88,z7,z34,z3,z4,z156]),(0,[z49,z1,z7,z37,z3,z6]),(0,[z1,z7,z4,z6,z158,z14])],[(0,[z1,z7,z2,z304,z6,z14]),(0,[z88,z7,z2,z16,z4,z156]),(0,[z63,z49,z1,z195,z3,z6]),(0,[z1,z7,z731,z2,z3,z6]),(0,[z1,z7,z57,z433,z4,z6]),(0,[z732,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z733,z4,z6])],[(0,[z1,z7,z2,z734,z4,z6]),(0,[z76,z1,z7,z276,z2,z6]),(0,[z63,z1,z67,z4,z6,z14]),(0,[z1,z7,z2,z243,z6,z14]),(0,[z735,z1,z7,z350,z3,z6]),(0,[z49,z1,z7,z3,z240,z6]),(0,[z1,z7,z2,z4,z6,z736])],[(0,[z1,z64,z140,z3,z4,z6]),(0,[z737,z1,z7,z2,z4,z6])],[(0,[z1,z7,z3,z4,z738,z6]),(0,[z1,z7,z2,z16,z6,z180]),(0,[z1,z7,z2,z739,z62,z6])],[(0,[z1,z7,z2,z3,z740,z6]),(0,[z1,z7,z2,z3,z741,z6])],[(0,[z259,z225,z1,z7,z4,z6]),(0,[z1,z7,z2,z742,z4,z6])],[(0,[z171,z2,z3,z4,z6,z156]),(0,[z272,z1,z2,z3,z743,z6]),(0,[z1,z7,z11,z593,z3,z6]),(0,[z1,z7,z26,z83,z4,z6]),(0,[z1,z7,z11,z2,z744,z6]),(0,[z136,z1,z7,z3,z4,z27])],[(0,[z1,z64,z3,z618,z4,z6]),(0,[z1,z7,z597,z83,z4,z6]),(0,[z1,z7,z2,z745,z6,z14])],[(0,[z164,z594,z2,z3,z4,z6]),(0,[z746,z1,z7,z3,z273,z6])],[(0,[z1,z7,z2,z4,z6,z747]),(0,[z1,z7,z2,z3,z748,z6]),(0,[z1,z7,z2,z4,z6,z749]),(0,[z1,z7,z2,z750,z6,z14])],[(0,[z1,z64,z140,z16,z4,z6]),(0,[z49,z1,z7,z3,z6,z629]),(0,[z1,z124,z11,z2,z3,z5]),(0,[z1,z7,z11,z57,z20,z6]),(0,[z751,z1,z7,z2,z4,z6])],[(0,[z1,z7,z2,z3,z4,z752]),(0,[z88,z7,z80,z3,z4,z156]),(0,[z35,z1,z2,z547,z4,z6]),(0,[z82,z73,z2,z3,z4,z25])],[(0,[z55,z1,z721,z7,z3,z6]),(0,[z7,z2,z3,z4,z6,z753]),(0,[z1,z7,z11,z2,z6,z749]),(0,[z111,z1,z7,z37,z3,z6]),(0,[z50,z1,z7,z2,z16,z6])],[(0,[z1,z239,z2,z3,z247,z6]),(0,[z49,z1,z7,z3,z635,z6]),(0,[z754,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z4,z6,z755]),(0,[z73,z7,z2,z3,z756,z6]),(0,[z1,z7,z265,z16,z4,z6])]],
   [[(0,[z1,z7,z2,z757,z4,z6]),(0,[z218,z7,z2,z159,z4,z6]),(0,[z1,z7,z758,z3,z4,z6]),(0,[z759,z1,z7,z2,z3,z6]),(0,[z136,z1,z7,z16,z4,z27])],[(0,[z1,z7,z2,z3,z760,z6])],[(0,[z761,z1,z7,z2,z3,z6]),(0,[z218,z7,z2,z4,z6,z410])],[(0,[z1,z124,z2,z3,z4,z346]),(0,[z570,z7,z2,z3,z19,z6])],[(0,[z49,z76,z1,z7,z2,z6]),(0,[z1,z7,z674,z251,z4,z6]),(0,[z1,z7,z16,z762,z4,z6])],[(0,[z1,z117,z2,z129,z6,z14]),(0,[z1,z7,z378,z4,z6,z158])],[(0,[z763,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z128,z130,z6])],[(0,[z259,z1,z7,z3,z4,z6]),(0,[z515,z7,z2,z132,z4,z6]),(0,[z1,z7,z3,z738,z162,z6]),(0,[z1,z7,z2,z4,z6,z725])],[(0,[z1,z7,z2,z764,z4,z6]),(0,[z269,z7,z2,z3,z765,z6]),(0,[z1,z7,z2,z16,z135,z6]),(0,[z118,z7,z11,z2,z3,z6])],[(0,[z63,z1,z133,z67,z3,z6]),(0,[z1,z7,z2,z3,z184,z6]),(0,[z1,z7,z2,z4,z489,z14])],[(0,[z1,z7,z2,z3,z6,z766]),(0,[z1,z464,z248,z2,z3,z6]),(0,[z1,z7,z11,z2,z6,z725]),(0,[z1,z7,z2,z3,z174,z767])],[(0,[z611,z7,z2,z3,z79,z6]),(0,[z1,z7,z8,z3,z4,z393]),(0,[z1,z7,z2,z3,z767,z31])],[],[(0,[z1,z768,z2,z3,z4,z6]),(0,[z1,z7,z2,z135,z6,z14]),(0,[z202,z1,z7,z11,z3,z6]),(0,[z49,z1,z7,z557,z3,z6]),(0,[z1,z7,z37,z3,z4,z6]),(0,[z1,z7,z4,z6,z14,z769])],[(0,[z49,z1,z7,z181,z3,z6]),(0,[z111,z1,z7,z2,z84,z6]),(0,[z441,z1,z7,z2,z58,z6])],[(0,[z1,z7,z2,z3,z770,z6]),(0,[z1,z7,z2,z3,z43,z6]),(0,[z771,z1,z7,z2,z3,z6]),(0,[z7,z2,z3,z4,z6,z772]),(0,[z1,z7,z2,z3,z773,z6]),(0,[z1,z7,z2,z3,z774,z6]),(0,[z1,z7,z265,z3,z30,z6]),(0,[z49,z1,z7,z8,z3,z489])]],
   [[(0,[z1,z775,z2,z3,z4,z6]),(0,[z81,z1,z2,z687,z4,z6]),(0,[z49,z111,z1,z7,z83,z6])],[(0,[z1,z7,z776,z3,z4,z6]),(0,[z7,z2,z3,z765,z4,z6]),(0,[z1,z7,z777,z83,z4,z6]),(0,[z1,z7,z57,z4,z6,z317]),(0,[z1,z7,z2,z128,z329,z6])],[(0,[z706,z41,z2,z3,z4,z6]),(0,[z1,z778,z2,z3,z4,z6]),(0,[z1,z7,z2,z779,z4,z6]),(0,[z82,z2,z3,z4,z364,z25]),(0,[z1,z7,z2,z58,z39,z6])],[(0,[z1,z7,z2,z780,z4,z6]),(0,[z1,z7,z2,z16,z4,z484]),(0,[z49,z1,z7,z8,z16,z6])],[(0,[z563,z1,z7,z2,z3,z489])],[(0,[z7,z2,z3,z4,z6,z781]),(0,[z1,z7,z276,z2,z6,z14]),(0,[z1,z7,z782,z2,z6,z14]),(0,[z1,z7,z37,z16,z4,z6])],[(0,[z388,z1,z2,z3,z4,z25]),(0,[z1,z7,z2,z3,z71,z6]),(0,[z49,z1,z7,z3,z783,z6]),(0,[z1,z7,z11,z3,z6,z158])],[(0,[z1,z7,z2,z16,z43,z6]),(0,[z49,z55,z1,z7,z16,z6]),(0,[z1,z7,z8,z3,z421,z6]),(0,[z1,z7,z720,z2,z3,z6])],[(0,[z1,z2,z3,z784,z4,z6]),(0,[z88,z2,z3,z4,z139,z156]),(0,[z49,z785,z7,z2,z3,z6])],[(0,[z661,z7,z13,z3,z4,z6]),(0,[z786,z1,z7,z2,z3,z6]),(0,[z91,z7,z2,z4,z89,z426]),(0,[z1,z7,z2,z787,z6,z14])],[(0,[z55,z7,z3,z665,z4,z6]),(0,[z49,z1,z7,z451,z3,z6]),(0,[z1,z7,z2,z3,z6,z303]),(0,[z1,z7,z230,z265,z3,z6])],[(0,[z1,z7,z2,z3,z238,z6]),(0,[z1,z7,z2,z3,z765,z6]),(0,[z1,z7,z11,z2,z294,z6]),(0,[z1,z7,z788,z3,z4,z6]),(0,[z1,z7,z3,z448,z134,z6]),(0,[z1,z7,z2,z4,z6,z122]),(0,[z1,z7,z2,z3,z789,z6]),(0,[z790,z1,z7,z2,z142,z6]),(0,[z1,z7,z720,z4,z6,z14])],[(0,[z63,z49,z1,z67,z3,z6]),(0,[z1,z7,z3,z6,z113,z769])],[(0,[z49,z1,z7,z187,z3,z6]),(0,[z49,z1,z7,z2,z93,z6]),(0,[z1,z7,z57,z20,z4,z6]),(0,[z1,z7,z2,z58,z84,z6]),(0,[z49,z1,z7,z240,z4,z6])],[(0,[z118,z7,z2,z3,z4,z6]),(0,[z791,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z4,z6,z792]),(0,[z1,z7,z2,z16,z71,z6]),(0,[z49,z793,z7,z2,z3,z6]),(0,[z1,z7,z11,z2,z6,z122])],[(0,[z1,z7,z2,z176,z4,z14]),(0,[z1,z7,z794,z3,z4,z6]),(0,[z1,z7,z2,z795,z4,z6]),(0,[z183,z7,z2,z4,z6,z14]),(0,[z49,z569,z1,z7,z3,z6]),(0,[z111,z1,z7,z2,z349,z6]),(0,[z50,z1,z7,z2,z6,z274])]],
   [[(0,[z1,z239,z11,z2,z3,z6]),(0,[z173,z1,z7,z2,z3,z489]),(0,[z1,z7,z2,z4,z6,z796])],[(0,[z1,z7,z2,z797,z4,z6]),(0,[z1,z7,z2,z3,z798,z6]),(1,[z7,z2,z3,z4,z772]),(0,[z746,z1,z7,z3,z4,z6])],[(0,[z1,z7,z2,z3,z799,z6])],[(0,[z164,z183,z2,z3,z4,z6]),(0,[z1,z2,z3,z30,z800,z6]),(0,[z1,z7,z11,z2,z6,z796]),(0,[z1,z7,z2,z16,z789,z6])],[(0,[z801,z1,z7,z2,z537,z6]),(0,[z1,z171,z2,z3,z247,z6]),(0,[z183,z7,z11,z2,z3,z6]),(0,[z49,z802,z1,z7,z2,z6])],[(0,[z1,z7,z2,z803,z4,z6]),(0,[z49,z1,z7,z704,z3,z6]),(0,[z63,z49,z1,z7,z6,z14]),(0,[z1,z117,z195,z2,z3,z6]),(0,[z56,z1,z7,z83,z4,z6]),(0,[z49,z1,z7,z11,z6,z14])],[(1,[z7,z804,z3,z4,z6]),(0,[z82,z1,z350,z3,z4,z25]),(0,[z49,z1,z7,z3,z280,z6])],[],[(0,[z87,z7,z2,z4,z6,z275]),(0,[z1,z7,z11,z2,z228,z6]),(0,[z1,z7,z2,z805,z4,z6])],[(0,[z81,z1,z2,z4,z6,z241]),(0,[z7,z2,z3,z4,z6,z806]),(0,[z1,z7,z2,z4,z306,z14]),(0,[z1,z7,z2,z16,z4,z435])],[(0,[z49,z87,z1,z7,z57,z6]),(0,[z1,z7,z2,z93,z4,z6]),(0,[z1,z7,z2,z16,z799,z6])],[(0,[z1,z171,z2,z3,z304,z6]),(0,[z807,z1,z7,z2,z4,z6]),(1,[z1,z713,z3,z4,z6]),(0,[z49,z1,z7,z3,z65,z6]),(0,[z1,z7,z11,z2,z808,z6])],[(0,[z809,z7,z2,z3,z4,z6])],[(0,[z810,z1,z7,z2,z4,z6]),(0,[z811,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z4,z389,z14]),(0,[z49,z1,z7,z2,z381,z6]),(0,[z1,z7,z2,z6,z14,z303])],[(0,[z1,z7,z2,z812,z4,z6]),(0,[z1,z7,z3,z4,z6,z813]),(0,[z1,z7,z2,z4,z814,z14])],[(0,[z76,z1,z7,z2,z4,z6]),(0,[z1,z7,z3,z4,z6,z815]),(0,[z1,z239,z2,z414,z4,z6]),(0,[z1,z7,z11,z2,z277,z6]),(0,[z49,z1,z7,z57,z3,z6]),(0,[z49,z816,z7,z2,z3,z6])]],
   [[(0,[z1,z7,z817,z2,z3,z6]),(0,[z1,z7,z133,z3,z6,z27]),(0,[z202,z111,z1,z7,z3,z6]),(0,[z1,z7,z2,z58,z62,z6])],[(0,[z103,z1,z67,z3,z4,z6]),(0,[z1,z7,z2,z3,z818,z6]),(0,[z1,z7,z2,z3,z756,z6]),(0,[z1,z7,z819,z2,z3,z6]),(0,[z1,z7,z2,z421,z6,z122])],[(0,[z88,z7,z2,z3,z4,z772]),(0,[z315,z1,z2,z3,z30,z6]),(0,[z183,z124,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z4,z459]),(0,[z49,z1,z7,z8,z3,z295])],[(0,[z820,z1,z7,z2,z3,z6]),(0,[z54,z49,z369,z7,z3,z6]),(0,[z49,z1,z7,z3,z6,z306]),(0,[z1,z7,z2,z3,z6,z821])],[(0,[z232,z7,z2,z415,z3,z6]),(0,[z1,z7,z2,z190,z4,z6])],[(0,[z91,z7,z2,z3,z4,z89]),(0,[z49,z1,z7,z695,z3,z6])],[(0,[z1,z239,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z4,z621])],[(0,[z1,z7,z3,z822,z4,z6]),(0,[z232,z7,z2,z3,z765,z6]),(0,[z1,z2,z16,z4,z6,z139])],[(0,[z1,z7,z11,z2,z329,z6]),(0,[z1,z7,z2,z4,z6,z53])],[(0,[z259,z1,z7,z3,z129,z6]),(0,[z823,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z3,z824,z6]),(0,[z825,z1,z7,z3,z4,z6]),(0,[z826,z1,z7,z2,z4,z6]),(0,[z49,z1,z7,z3,z162,z6])],[(0,[z1,z7,z2,z3,z827,z6]),(0,[z1,z7,z2,z3,z828,z6])],[(0,[z0,z171,z2,z3,z4,z6]),(0,[z829,z1,z2,z3,z4,z6]),(0,[z1,z7,z11,z2,z6,z53]),(0,[z1,z830,z2,z4,z6,z14])],[(0,[z1,z7,z2,z831,z4,z6])],[(0,[z155,z7,z11,z2,z159,z6]),(0,[z91,z7,z2,z16,z4,z89]),(0,[z735,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z832,z4,z6]),(0,[z1,z7,z2,z4,z6,z833])],[(0,[z1,z7,z2,z16,z4,z144]),(0,[z1,z7,z2,z834,z4,z6]),(0,[z1,z7,z3,z17,z6,z180])],[(0,[z297,z49,z1,z7,z3,z6]),(0,[z49,z1,z7,z57,z20,z6]),(0,[z1,z7,z2,z16,z4,z642])]],
   [[(0,[z403,z7,z2,z3,z79,z6]),(0,[z1,z171,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z174,z614])],[(0,[z835,z1,z7,z3,z4,z6]),(0,[z49,z266,z1,z7,z3,z6]),(0,[z87,z7,z11,z2,z132,z6]),(0,[z836,z1,z7,z3,z4,z6]),(0,[z1,z7,z2,z837,z4,z6])],[(0,[z259,z1,z7,z228,z4,z6]),(0,[z1,z7,z2,z414,z247,z6]),(0,[z73,z7,z2,z3,z818,z6]),(0,[z49,z1,z838,z2,z3,z6])],[(0,[z1,z7,z2,z4,z6,z839]),(0,[z829,z1,z2,z16,z4,z6])],[(0,[z155,z7,z465,z2,z4,z6]),(0,[z840,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z3,z841,z6]),(0,[z141,z1,z7,z2,z340,z6])],[(0,[z1,z7,z2,z4,z6,z842]),(0,[z1,z7,z843,z3,z4,z6]),(0,[z1,z171,z11,z2,z3,z6]),(0,[z49,z35,z1,z7,z57,z6]),(0,[z1,z7,z844,z2,z3,z6]),(0,[z1,z7,z2,z3,z6,z845]),(0,[z332,z1,z7,z2,z349,z6])],[(0,[z49,z1,z7,z3,z165,z6]),(0,[z1,z7,z846,z2,z3,z6]),(0,[z1,z7,z2,z847,z4,z6])],[(0,[z1,z7,z3,z848,z4,z6]),(0,[z849,z1,z7,z2,z3,z4])],[(0,[z850,z1,z7,z2,z6,z426])],[(0,[z1,z239,z80,z3,z4,z6]),(0,[z1,z7,z2,z414,z304,z6]),(0,[z1,z7,z2,z3,z851,z6]),(0,[z1,z7,z2,z3,z421,z6]),(0,[z1,z7,z2,z852,z6,z14])],[(0,[z1,z7,z2,z4,z6,z853]),(0,[z445,z1,z2,z69,z4,z6]),(0,[z103,z49,z1,z7,z3,z6]),(0,[z1,z7,z2,z6,z14,z854]),(0,[z50,z1,z7,z2,z16,z14])],[(0,[z1,z7,z2,z855,z4,z6]),(0,[z1,z7,z11,z3,z182,z6]),(0,[z1,z7,z2,z4,z6,z856])],[(0,[z1,z7,z2,z4,z6,z857])],[(0,[z1,z7,z2,z16,z4,z361]),(0,[z1,z7,z2,z3,z858,z6]),(0,[z1,z11,z2,z3,z6,z139])],[(0,[z49,z1,z287,z7,z3,z6]),(0,[z49,z661,z1,z7,z3,z6])],[(0,[z1,z7,z2,z3,z4,z859]),(0,[z49,z1,z7,z2,z489,z14]),(0,[z1,z7,z2,z16,z4,z681])]],
   [[(0,[z1,z7,z2,z3,z860,z6]),(0,[z1,z7,z2,z3,z861,z6]),(0,[z1,z7,z2,z862,z4,z6])],[(0,[z55,z1,z114,z7,z3,z6]),(0,[z63,z1,z67,z3,z4,z6])],[(0,[z1,z7,z863,z2,z3,z6]),(0,[z232,z259,z1,z7,z3,z6]),(0,[z259,z1,z7,z16,z4,z6]),(0,[z1,z7,z2,z3,z6,z864]),(0,[z49,z1,z7,z57,z261,z6])],[(0,[z1,z7,z2,z865,z4,z6]),(0,[z1,z2,z123,z866,z4,z6]),(0,[z1,z7,z2,z867,z4,z6])],[(0,[z73,z42,z2,z3,z4,z6]),(0,[z1,z171,z2,z414,z4,z6]),(0,[z1,z7,z2,z3,z750,z6]),(0,[z202,z1,z117,z7,z3,z6]),(0,[z118,z7,z2,z3,z119,z6]),(0,[z1,z7,z2,z16,z184,z6]),(0,[z1,z7,z2,z16,z4,z481]),(0,[z1,z7,z8,z3,z121,z303])],[(0,[z1,z7,z2,z3,z868,z6]),(0,[z1,z7,z2,z3,z869,z6]),(0,[z870,z1,z7,z2,z3,z6]),(0,[z1,z464,z2,z3,z129,z6]),(0,[z70,z1,z7,z11,z2,z6]),(0,[z1,z124,z2,z3,z4,z5]),(0,[z1,z7,z11,z2,z6,z148]),(0,[z1,z7,z2,z871,z4,z6]),(0,[z1,z7,z8,z4,z121,z122])],[(0,[z872,z7,z2,z3,z4,z6]),(0,[z458,z1,z7,z2,z6,z14]),(0,[z49,z1,z7,z57,z16,z6])],[(0,[z54,z7,z276,z9,z3,z6]),(0,[z1,z7,z2,z3,z873,z6]),(0,[z1,z7,z2,z3,z6,z874]),(0,[z49,z1,z7,z11,z58,z6]),(0,[z1,z7,z2,z875,z4,z6])],[(0,[z1,z7,z2,z3,z876,z6])],[(0,[z1,z7,z2,z3,z877,z6]),(0,[z49,z1,z7,z3,z6,z158]),(0,[z515,z7,z2,z28,z4,z6])],[(0,[z1,z7,z276,z2,z3,z6]),(0,[z878,z1,z7,z2,z3,z6]),(0,[z259,z269,z1,z7,z3,z6]),(0,[z879,z7,z2,z3,z4,z6]),(0,[z1,z7,z8,z3,z4,z880])],[(0,[z1,z7,z2,z4,z348,z14]),(0,[z81,z1,z2,z586,z4,z6]),(0,[z82,z1,z552,z3,z4,z25]),(0,[z85,z50,z1,z7,z2,z14])],[(0,[z49,z1,z360,z7,z3,z6]),(0,[z790,z1,z7,z2,z3,z6])],[(0,[z1,z124,z2,z16,z4,z5]),(0,[z881,z1,z2,z4,z6,z14])],[(0,[z49,z1,z7,z2,z294,z6]),(0,[z1,z7,z2,z6,z882,z14])],[(0,[z883,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z4,z6,z884]),(0,[z1,z7,z2,z885,z4,z6])]],
   [[(0,[z1,z7,z2,z3,z886,z6]),(0,[z1,z7,z3,z17,z43,z6]),(0,[z202,z70,z1,z7,z4,z6]),(0,[z1,z7,z2,z3,z6,z887]),(0,[z1,z7,z2,z3,z6,z888])],[(0,[z0,z42,z2,z3,z537,z6]),(0,[z1,z7,z889,z3,z4,z6]),(0,[z1,z7,z3,z83,z71,z6]),(0,[z161,z369,z7,z2,z3,z6]),(0,[z49,z1,z7,z2,z6,z122]),(0,[z1,z7,z2,z3,z890,z6])],[(0,[z259,z1,z7,z3,z30,z6]),(0,[z1,z7,z11,z8,z3,z121]),(0,[z1,z7,z265,z3,z62,z6]),(0,[z1,z7,z2,z3,z174,z52])],[(0,[z49,z118,z7,z2,z3,z6]),(0,[z1,z7,z11,z350,z3,z6]),(0,[z1,z7,z2,z244,z184,z6]),(0,[z111,z1,z7,z134,z4,z6])],[(0,[z315,z1,z2,z3,z800,z6])],[(0,[z1,z7,z2,z3,z891,z6]),(0,[z892,z1,z7,z2,z3,z6]),(0,[z893,z1,z7,z3,z4,z6]),(0,[z1,z7,z2,z16,z6,z303])],[(0,[z1,z114,z7,z8,z3,z6]),(0,[z154,z49,z1,z7,z3,z6]),(0,[z1,z7,z2,z16,z238,z6]),(0,[z315,z1,z2,z30,z6,z14]),(0,[z1,z7,z2,z192,z4,z6])],[(0,[z164,z894,z2,z3,z4,z6]),(0,[z70,z1,z7,z182,z4,z6]),(0,[z396,z1,z7,z2,z4,z14]),(0,[z85,z1,z7,z11,z2,z14]),(0,[z1,z7,z2,z895,z4,z6])],[(0,[z896,z7,z2,z3,z4,z6]),(0,[z1,z7,z20,z777,z4,z6]),(0,[z1,z7,z11,z2,z6,z14]),(0,[z1,z7,z37,z3,z174,z6])],[(0,[z7,z2,z3,z19,z765,z6]),(0,[z118,z7,z2,z16,z4,z6]),(0,[z85,z49,z1,z7,z2,z14]),(0,[z1,z7,z2,z302,z58,z6]),(0,[z136,z1,z7,z4,z27,z14]),(0,[z1,z7,z2,z16,z890,z6])],[(0,[z1,z7,z2,z224,z6,z14]),(0,[z63,z49,z1,z7,z3,z6]),(0,[z1,z7,z3,z182,z243,z6]),(0,[z49,z1,z7,z11,z3,z6]),(0,[z1,z7,z559,z2,z3,z39])],[(0,[z49,z1,z7,z2,z228,z6]),(0,[z49,z183,z7,z2,z3,z6]),(0,[z897,z1,z7,z2,z3,z6])],[(0,[z898,z1,z7,z2,z6,z14]),(0,[z1,z7,z2,z899,z4,z6]),(0,[z1,z7,z11,z2,z142,z6])],[(0,[z1,z7,z2,z3,z900,z6])],[(0,[z1,z7,z2,z3,z901,z6]),(0,[z1,z7,z2,z3,z902,z6]),(0,[z1,z7,z2,z4,z903,z6]),(0,[z1,z7,z2,z3,z904,z6]),(0,[z1,z7,z2,z905,z4,z6]),(0,[z1,z7,z350,z381,z4,z6]),(0,[z1,z7,z11,z17,z6,z14]),(0,[z1,z7,z2,z6,z122,z303])],[(0,[z1,z7,z133,z2,z109,z6])]],
   [[(0,[z183,z7,z2,z3,z119,z6])],[(0,[z55,z7,z13,z4,z6,z14]),(0,[z70,z1,z7,z2,z19,z6])],[(0,[z1,z906,z2,z3,z4,z6]),(0,[z670,z49,z1,z7,z3,z6]),(0,[z49,z1,z7,z2,z277,z6]),(0,[z1,z7,z2,z6,z845,z148])],[(0,[z1,z7,z2,z3,z907,z6]),(0,[z173,z1,z7,z2,z14,z31])],[(0,[z82,z49,z1,z2,z3,z25]),(0,[z1,z7,z2,z448,z21,z6]),(0,[z1,z7,z11,z2,z908,z6]),(0,[z1,z7,z2,z3,z6,z113])],[(0,[z1,z7,z2,z3,z909,z6]),(0,[z1,z7,z910,z3,z4,z6]),(0,[z1,z7,z911,z3,z4,z6]),(0,[z1,z7,z57,z20,z84,z6]),(0,[z394,z1,z2,z4,z6,z241])],[(0,[z1,z7,z912,z3,z4,z6]),(0,[z1,z2,z3,z866,z4,z6]),(0,[z49,z1,z7,z3,z434,z6])],[(0,[z1,z7,z2,z913,z4,z6]),(0,[z914,z7,z2,z3,z4,z6])],[(0,[z111,z1,z7,z2,z228,z6]),(0,[z1,z7,z80,z4,z6,z14]),(0,[z915,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z16,z4,z525]),(0,[z118,z7,z2,z244,z4,z6]),(0,[z1,z2,z3,z4,z6,z916]),(0,[z1,z7,z2,z6,z180,z917]),(0,[z1,z7,z2,z918,z4,z6])],[(0,[z1,z7,z2,z4,z6,z919]),(0,[z173,z1,z7,z265,z3,z6]),(0,[z1,z7,z720,z3,z4,z6])],[(0,[z1,z7,z2,z3,z224,z6]),(0,[z1,z7,z2,z3,z920,z6]),(0,[z49,z55,z7,z13,z3,z6]),(0,[z49,z155,z7,z2,z159,z6]),(0,[z1,z7,z2,z16,z4,z530]),(0,[z499,z1,z7,z2,z240,z6]),(0,[z1,z7,z2,z3,z6,z854])],[(0,[z82,z1,z2,z3,z4,z591]),(0,[z49,z1,z7,z2,z329,z6]),(0,[z1,z7,z2,z421,z6,z14])],[(0,[z1,z7,z2,z3,z6,z921]),(0,[z1,z7,z922,z3,z4,z6]),(0,[z746,z81,z1,z7,z3,z6]),(0,[z49,z1,z124,z2,z3,z5]),(0,[z49,z1,z7,z3,z6,z180]),(0,[z1,z7,z2,z16,z6,z113])],[(0,[z183,z7,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z100]),(0,[z1,z7,z276,z2,z169,z6]),(0,[z232,z7,z2,z3,z19,z6]),(0,[z315,z1,z2,z16,z30,z6]),(0,[z1,z7,z2,z3,z6,z923]),(0,[z924,z7,z2,z4,z6,z14])],[(0,[z1,z7,z2,z3,z925,z6]),(0,[z1,z7,z926,z3,z4,z6]),(0,[z1,z7,z2,z927,z4,z6]),(0,[z49,z272,z1,z2,z3,z6]),(0,[z1,z7,z133,z8,z3,z6]),(0,[z49,z1,z7,z2,z6,z53])],[(0,[z1,z7,z928,z3,z4,z6]),(0,[z1,z7,z11,z80,z3,z6]),(0,[z111,z1,z7,z2,z277,z6]),(0,[z49,z1,z7,z3,z6,z331]),(0,[z49,z1,z7,z2,z929,z6]),(0,[z1,z7,z2,z16,z4,z479]),(0,[z218,z50,z1,z7,z2,z6])]],
   [[(0,[z930,z1,z7,z2,z3,z6]),(0,[z1,z239,z34,z3,z4,z6])],[(0,[z1,z7,z2,z931,z4,z6]),(0,[z1,z7,z276,z2,z16,z6]),(1,[z786,z1,z7,z3,z6]),(0,[z1,z239,z2,z16,z4,z6]),(0,[z1,z7,z2,z4,z6,z932])],[(0,[z42,z2,z3,z4,z6,z591]),(0,[z1,z7,z2,z933,z4,z6]),(0,[z49,z70,z1,z7,z2,z6]),(0,[z7,z2,z4,z6,z364,z14])],[(0,[z934,z1,z7,z2,z4,z6])],[(0,[z1,z935,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z936,z6]),(0,[z7,z2,z16,z4,z6,z364]),(0,[z1,z7,z3,z134,z4,z6]),(0,[z49,z1,z7,z16,z162,z6]),(0,[z1,z7,z2,z21,z6,z113])],[(0,[z88,z7,z2,z3,z4,z591]),(0,[z232,z7,z2,z16,z19,z6]),(0,[z63,z1,z713,z3,z4,z6]),(0,[z56,z1,z7,z323,z4,z6]),(0,[z183,z7,z2,z16,z4,z6])],[(0,[z1,z7,z2,z937,z4,z6]),(0,[z82,z1,z2,z381,z4,z25])],[(0,[z41,z894,z2,z3,z4,z6]),(0,[z91,z7,z2,z294,z4,z89]),(0,[z49,z1,z64,z140,z3,z6]),(0,[z1,z7,z2,z938,z4,z6]),(0,[z49,z737,z1,z7,z2,z6])],[(0,[z272,z183,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z939,z6]),(0,[z940,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z3,z941,z6]),(0,[z441,z1,z7,z2,z3,z110]),(0,[z111,z1,z7,z2,z329,z6])],[(0,[z88,z7,z2,z357,z4,z156]),(0,[z1,z7,z2,z942,z4,z6]),(0,[z1,z7,z11,z3,z6,z675])],[(0,[z225,z269,z7,z2,z79,z6]),(0,[z1,z7,z943,z2,z3,z6]),(0,[z1,z7,z2,z3,z944,z6])],[(0,[z54,z1,z114,z7,z3,z6]),(0,[z1,z7,z2,z3,z243,z6]),(0,[z35,z1,z2,z866,z4,z6]),(0,[z111,z1,z7,z2,z6,z53]),(0,[z1,z7,z2,z4,z14,z250])],[(0,[z1,z7,z2,z945,z4,z6]),(0,[z1,z7,z2,z3,z247,z6]),(0,[z391,z1,z7,z2,z4,z6]),(0,[z50,z81,z1,z7,z2,z6])],[(0,[z946,z1,z7,z2,z3,z6])],[(0,[z1,z7,z2,z947,z4,z6]),(0,[z49,z1,z7,z3,z182,z6]),(0,[z1,z7,z4,z6,z14,z948])],[]],
   [[(0,[z1,z7,z2,z949,z4,z6]),(0,[z786,z1,z7,z3,z271,z6]),(0,[z1,z7,z2,z271,z6,z14]),(0,[z1,z7,z2,z6,z950,z426]),(0,[z1,z7,z3,z777,z4,z6])],[(0,[z49,z164,z41,z2,z3,z6]),(0,[z49,z1,z239,z2,z3,z6]),(0,[z63,z49,z1,z7,z16,z6]),(0,[z49,z1,z7,z11,z16,z6])],[(0,[z1,z7,z951,z3,z4,z6]),(0,[z1,z952,z2,z3,z4,z6]),(0,[z49,z1,z7,z6,z14,z331]),(0,[z50,z394,z1,z7,z2,z6]),(0,[z1,z7,z2,z16,z944,z6])],[(0,[z1,z7,z2,z3,z304,z6]),(0,[z202,z1,z7,z3,z19,z6]),(0,[z1,z7,z34,z3,z247,z6]),(0,[z1,z7,z2,z16,z243,z6]),(0,[z460,z7,z2,z415,z3,z6]),(0,[z1,z7,z11,z2,z192,z6])],[(0,[z483,z7,z2,z3,z79,z6]),(0,[z183,z7,z2,z244,z4,z6]),(0,[z1,z7,z2,z119,z6,z14]),(0,[z141,z49,z1,z7,z83,z6]),(0,[z1,z7,z2,z3,z953,z6]),(0,[z1,z7,z2,z16,z421,z6])],[(0,[z954,z1,z7,z2,z4,z6]),(0,[z1,z7,z66,z2,z6,z14]),(0,[z1,z7,z2,z4,z6,z148]),(0,[z1,z7,z11,z2,z955,z6]),(0,[z7,z2,z4,z6,z956,z14])],[(0,[z35,z1,z2,z69,z4,z6])],[(0,[z1,z7,z2,z4,z6,z957]),(0,[z1,z7,z2,z3,z958,z6]),(0,[z1,z7,z2,z3,z448,z6]),(0,[z1,z7,z248,z2,z58,z6])],[(0,[z55,z7,z804,z3,z4,z6]),(0,[z49,z1,z7,z2,z6,z148]),(0,[z1,z7,z2,z329,z4,z6])],[(0,[z1,z830,z2,z3,z4,z6]),(0,[z1,z7,z3,z959,z271,z6]),(0,[z49,z1,z7,z83,z21,z6])],[(0,[z1,z7,z34,z3,z304,z6]),(0,[z1,z7,z2,z3,z960,z6]),(0,[z7,z11,z2,z3,z6,z364]),(0,[z1,z7,z11,z2,z58,z6]),(0,[z1,z7,z2,z128,z739,z6])],[(0,[z388,z1,z7,z2,z4,z14]),(0,[z54,z199,z7,z3,z4,z6]),(0,[z1,z7,z2,z3,z961,z6]),(0,[z225,z1,z7,z11,z2,z6]),(0,[z1,z7,z2,z16,z304,z6]),(0,[z458,z1,z7,z2,z3,z6])],[(0,[z962,z1,z7,z2,z3,z6]),(0,[z63,z1,z67,z16,z4,z6]),(0,[z1,z7,z2,z16,z953,z6])],[(0,[z7,z2,z963,z159,z4,z6]),(0,[z1,z7,z782,z2,z3,z6]),(0,[z49,z1,z171,z2,z3,z6]),(0,[z391,z1,z7,z133,z2,z6]),(0,[z183,z2,z3,z4,z6,z25])],[(0,[z1,z171,z2,z3,z4,z6]),(0,[z49,z1,z7,z3,z43,z6]),(0,[z1,z64,z713,z3,z4,z6]),(0,[z1,z64,z7,z731,z3,z6]),(0,[z81,z1,z11,z2,z123,z6]),(0,[z1,z7,z2,z964,z4,z6])],[(0,[z965,z1,z7,z2,z3,z6]),(0,[z1,z7,z80,z3,z247,z6]),(0,[z966,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z967,z243,z6]),(0,[z1,z7,z968,z3,z4,z6]),(0,[z35,z1,z573,z2,z4,z6]),(0,[z1,z7,z2,z16,z448,z6]),(0,[z1,z7,z3,z4,z6,z880]),(0,[z1,z7,z8,z4,z121,z14])]],
   [[(0,[z962,z0,z1,z7,z3,z6]),(0,[z56,z458,z1,z7,z83,z6])],[(0,[z1,z7,z3,z4,z6,z158])],[(0,[z1,z7,z2,z797,z537,z6]),(0,[z1,z7,z2,z537,z6,z14]),(0,[z1,z7,z969,z2,z3,z6]),(0,[z88,z49,z7,z2,z3,z156]),(0,[z1,z7,z3,z182,z4,z6]),(0,[z49,z1,z7,z3,z83,z6])],[(0,[z1,z7,z2,z970,z4,z6]),(0,[z111,z1,z7,z2,z658,z6]),(0,[z1,z7,z552,z381,z4,z6]),(0,[z1,z7,z2,z4,z6,z971])],[(0,[z1,z7,z2,z3,z972,z6]),(0,[z1,z7,z2,z973,z4,z6]),(0,[z1,z7,z2,z3,z739,z6]),(0,[z1,z7,z2,z3,z974,z6]),(0,[z1,z7,z2,z174,z52,z53])],[(0,[z269,z7,z2,z228,z79,z6]),(0,[z259,z1,z7,z3,z174,z6]),(0,[z1,z7,z2,z3,z174,z413]),(0,[z1,z171,z34,z3,z4,z6]),(0,[z82,z1,z2,z3,z184,z25]),(0,[z49,z1,z7,z8,z3,z121])],[(0,[z975,z1,z7,z2,z4,z6]),(0,[z1,z171,z2,z16,z4,z6]),(0,[z1,z7,z80,z3,z304,z6]),(0,[z49,z1,z7,z350,z3,z6]),(0,[z49,z1,z7,z2,z6,z971]),(0,[z173,z1,z7,z2,z3,z767])],[],[(0,[z1,z7,z2,z4,z6,z14]),(1,[z1,z7,z2,z739,z6])],[(0,[z1,z7,z11,z2,z976,z6])],[(0,[z54,z7,z11,z9,z3,z6]),(0,[z49,z1,z7,z656,z3,z6]),(0,[z1,z7,z977,z3,z4,z6]),(0,[z49,z1,z7,z16,z83,z6])],[(0,[z1,z7,z2,z3,z978,z6]),(0,[z979,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z980,z4,z6]),(0,[z1,z7,z2,z3,z981,z6]),(0,[z431,z49,z1,z7,z3,z6]),(0,[z1,z64,z140,z3,z135,z6]),(0,[z982,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z83,z6,z14]),(0,[z49,z1,z7,z2,z6,z14])],[(0,[z1,z7,z983,z3,z4,z6]),(0,[z1,z7,z2,z16,z974,z6])],[(0,[z1,z7,z11,z2,z3,z6]),(0,[z7,z2,z3,z4,z89,z469]),(0,[z269,z7,z2,z3,z79,z6]),(0,[z1,z7,z2,z16,z174,z52])],[(0,[z87,z7,z2,z452,z4,z6]),(0,[z1,z7,z2,z3,z984,z6]),(0,[z1,z7,z2,z210,z6,z14]),(0,[z1,z7,z2,z453,z130,z6]),(0,[z1,z7,z37,z3,z6,z31])],[(0,[z1,z7,z2,z4,z591,z14]),(0,[z73,z171,z2,z3,z4,z6]),(0,[z1,z7,z34,z4,z6,z14]),(0,[z272,z1,z2,z4,z6,z14]),(0,[z1,z7,z2,z3,z985,z6]),(0,[z1,z7,z986,z2,z3,z6]),(0,[z49,z1,z7,z2,z142,z6])]],
   [[(0,[z1,z7,z2,z3,z987,z6]),(0,[z49,z1,z7,z466,z3,z6]),(0,[z49,z988,z1,z7,z2,z6])],[(0,[z460,z259,z1,z7,z3,z6]),(0,[z1,z171,z80,z3,z4,z6]),(0,[z1,z2,z866,z69,z4,z6]),(0,[z989,z1,z7,z2,z4,z6]),(0,[z136,z1,z7,z3,z4,z880]),(0,[z1,z7,z134,z4,z6,z14]),(0,[z445,z1,z2,z4,z6,z32])],[(0,[z155,z7,z2,z963,z4,z6]),(0,[z49,z1,z7,z231,z3,z6]),(0,[z1,z7,z2,z990,z6,z14])],[(0,[z1,z7,z991,z3,z4,z6]),(0,[z49,z1,z7,z2,z899,z6]),(0,[z982,z7,z2,z16,z4,z6])],[(0,[z54,z7,z9,z4,z6,z14]),(0,[z1,z7,z204,z4,z6,z14]),(0,[z1,z7,z2,z3,z992,z6]),(0,[z49,z1,z125,z7,z3,z6]),(0,[z1,z7,z2,z21,z739,z6]),(0,[z7,z2,z16,z993,z4,z6])],[(0,[z269,z7,z2,z16,z79,z6]),(0,[z1,z7,z2,z58,z21,z6]),(0,[z994,z1,z7,z2,z4,z6]),(0,[z1,z7,z559,z37,z3,z6]),(0,[z1,z7,z37,z378,z4,z6])],[(0,[z1,z7,z2,z4,z572,z14])],[(0,[z1,z7,z2,z4,z6,z995]),(0,[z72,z1,z7,z2,z6,z14])],[(0,[z1,z7,z2,z3,z996,z6]),(0,[z1,z7,z2,z997,z4,z6]),(0,[z1,z7,z11,z354,z3,z6]),(0,[z202,z1,z7,z128,z3,z6]),(0,[z50,z1,z7,z2,z62,z6])],[(0,[z73,z7,z2,z4,z6,z14]),(0,[z49,z1,z7,z8,z3,z27]),(0,[z1,z7,z2,z261,z21,z6])],[(0,[z54,z49,z1,z7,z6,z14]),(0,[z1,z7,z2,z4,z6,z998])],[(0,[z49,z1,z7,z286,z3,z6]),(0,[z1,z7,z2,z3,z999,z6]),(0,[z1000,z1,z7,z2,z4,z6]),(0,[z1,z443,z2,z3,z30,z6]),(0,[z881,z1,z2,z3,z4,z6]),(0,[z1,z7,z8,z190,z4,z121])],[(0,[z1,z7,z2,z3,z4,z1001]),(0,[z1,z7,z2,z414,z4,z6]),(0,[z82,z73,z2,z3,z4,z6]),(0,[z49,z1,z160,z7,z3,z6])],[],[(0,[z7,z804,z9,z3,z4,z6]),(0,[z786,z1,z7,z3,z4,z6]),(0,[z50,z87,z1,z7,z2,z6]),(0,[z73,z7,z11,z2,z3,z6]),(0,[z1,z7,z3,z4,z6,z769])],[(0,[z1,z721,z7,z2,z3,z6]),(0,[z1,z7,z2,z1002,z4,z6]),(0,[z1003,z7,z2,z3,z4,z6]),(1,[z1,z7,z3,z4,z880])]],
   [[(0,[z1,z7,z659,z2,z4,z14]),(0,[z1,z2,z3,z4,z6,z716])],[(0,[z1,z7,z2,z3,z1004,z6]),(0,[z1,z7,z2,z1005,z4,z6]),(0,[z1006,z1,z7,z3,z4,z6])],[(0,[z678,z49,z1,z7,z3,z6]),(0,[z49,z1,z7,z80,z3,z6]),(0,[z1007,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z6,z1008]),(0,[z458,z1,z7,z2,z16,z6]),(0,[z445,z50,z1,z7,z2,z6])],[(0,[z1,z7,z2,z3,z4,z1009]),(0,[z1,z7,z34,z414,z4,z6]),(0,[z1,z2,z3,z800,z4,z6]),(0,[z1,z7,z277,z182,z4,z6])],[(0,[z1010,z1,z2,z3,z4,z6]),(0,[z1,z360,z140,z3,z4,z6])],[(0,[z1,z7,z2,z16,z224,z6]),(0,[z1,z7,z2,z3,z6,z1011]),(0,[z1,z713,z67,z3,z4,z6])],[(0,[z87,z7,z2,z132,z238,z6]),(0,[z1,z7,z11,z3,z17,z6])],[(0,[z1,z7,z3,z959,z4,z6]),(0,[z1,z7,z2,z1012,z3,z6]),(0,[z1,z7,z2,z601,z4,z14]),(0,[z1,z7,z2,z3,z1013,z6]),(0,[z49,z1,z7,z3,z6,z517]),(0,[z611,z7,z290,z2,z3,z6])],[(0,[z1,z7,z2,z1014,z4,z6])],[(0,[z1,z7,z1015,z2,z3,z6]),(0,[z1,z7,z2,z448,z6,z14])],[(0,[z1,z64,z11,z140,z3,z6]),(0,[z49,z1,z7,z731,z3,z6]),(0,[z82,z1,z2,z4,z25,z14]),(0,[z1,z7,z3,z174,z52,z158])],[(0,[z1,z7,z2,z1016,z4,z6]),(0,[z1,z7,z2,z3,z1017,z6]),(0,[z1,z7,z11,z10,z3,z6])],[(0,[z164,z41,z2,z4,z6,z14]),(0,[z49,z1,z952,z2,z3,z6])],[(0,[z1,z7,z2,z3,z1018,z6]),(0,[z49,z1,z7,z3,z279,z6]),(0,[z136,z1,z7,z11,z3,z27])],[(0,[z1019,z7,z2,z3,z4,z6]),(0,[z291,z49,z1,z7,z3,z6]),(0,[z1,z7,z11,z16,z17,z6])],[(0,[z1020,z1,z7,z2,z4,z6]),(0,[z55,z7,z13,z3,z4,z6]),(0,[z1,z7,z80,z414,z4,z6]),(0,[z49,z1,z7,z131,z3,z6]),(0,[z1,z7,z2,z3,z4,z880])]],
   [[(0,[z1,z7,z2,z228,z271,z6]),(0,[z70,z1,z7,z2,z79,z6]),(0,[z1,z7,z2,z3,z6,z1021]),(0,[z49,z1,z64,z7,z6,z14]),(0,[z1,z7,z2,z16,z4,z383]),(0,[z1,z7,z350,z3,z184,z6])],[(0,[z351,z1,z7,z2,z3,z295]),(0,[z1022,z7,z2,z4,z6,z14]),(0,[z1,z7,z2,z174,z52,z14])],[(0,[z54,z7,z804,z3,z4,z6]),(0,[z1,z7,z804,z3,z4,z6]),(0,[z49,z1,z7,z3,z6,z541]),(0,[z82,z118,z2,z3,z4,z25]),(0,[z136,z1,z7,z126,z4,z27])],[(0,[z1,z7,z2,z3,z1023,z6]),(0,[z1,z7,z2,z3,z6,z950])],[(0,[z1,z7,z2,z3,z990,z6]),(0,[z49,z1,z7,z3,z546,z6]),(0,[z1,z7,z11,z2,z16,z6]),(0,[z49,z1,z1024,z2,z3,z6])],[(0,[z173,z1,z7,z2,z3,z435])],[(0,[z1,z7,z674,z20,z4,z6]),(0,[z49,z1,z7,z2,z192,z6]),(0,[z1,z7,z2,z1025,z4,z6])],[(0,[z1,z7,z1026,z2,z3,z6]),(0,[z55,z7,z13,z16,z4,z6]),(0,[z1,z7,z2,z16,z247,z6]),(0,[z118,z7,z552,z3,z4,z6])],[(0,[z1,z7,z2,z3,z271,z6]),(0,[z607,z49,z1,z7,z3,z6]),(0,[z1,z7,z2,z3,z6,z1027]),(0,[z1,z7,z11,z2,z126,z6])],[(0,[z1028,z1,z7,z2,z43,z6]),(0,[z1,z7,z2,z733,z6,z180])],[(0,[z1,z7,z2,z4,z1029,z6]),(0,[z1,z7,z66,z2,z3,z6]),(0,[z202,z1,z7,z4,z6,z14]),(0,[z112,z1,z7,z4,z6,z331])],[(0,[z1,z7,z2,z247,z6,z14]),(0,[z924,z7,z2,z3,z4,z6]),(0,[z1,z7,z181,z4,z6,z317])],[(0,[z1,z7,z2,z3,z1030,z6]),(0,[z1,z7,z2,z3,z1031,z6]),(0,[z369,z7,z2,z3,z19,z6]),(0,[z1,z7,z3,z17,z243,z6]),(0,[z335,z1,z7,z2,z4,z14])],[(0,[z1,z7,z2,z58,z19,z6]),(0,[z1032,z7,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z716,z25]),(0,[z49,z1,z7,z2,z58,z6]),(0,[z1,z7,z265,z128,z21,z6])],[(0,[z478,z7,z2,z3,z79,z6]),(0,[z49,z1,z7,z57,z340,z6]),(0,[z49,z1,z464,z7,z3,z6])],[(0,[z1,z7,z2,z3,z273,z6])]],
   [[(0,[z1,z7,z2,z3,z1033,z6]),(0,[z41,z73,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z271,z6]),(0,[z1,z7,z2,z1034,z4,z6]),(0,[z49,z1,z7,z3,z6,z574])],[(0,[z291,z7,z9,z3,z4,z6]),(0,[z1,z7,z2,z3,z1035,z6]),(0,[z272,z1,z2,z3,z958,z6]),(0,[z1,z1036,z7,z2,z3,z6]),(0,[z1,z7,z1037,z3,z4,z6]),(0,[z49,z1,z7,z3,z107,z6]),(0,[z111,z1,z7,z2,z6,z113])],[(0,[z1,z7,z2,z1038,z4,z6]),(0,[z1039,z1,z7,z2,z3,z6])],[(0,[z1,z7,z2,z273,z6,z14]),(0,[z49,z1,z7,z3,z587,z6])],[(0,[z1,z2,z3,z4,z6,z139]),(0,[z1,z2,z3,z4,z6,z1040]),(0,[z1,z7,z2,z1041,z4,z6]),(1,[z49,z1,z7,z240,z6]),(0,[z1,z7,z2,z3,z1042,z6])],[(0,[z54,z7,z169,z9,z4,z6]),(0,[z1,z7,z3,z204,z43,z6]),(0,[z118,z7,z350,z3,z4,z6]),(0,[z49,z1,z7,z3,z6,z580]),(0,[z136,z72,z1,z7,z3,z27])],[(0,[z164,z272,z2,z3,z4,z6]),(0,[z49,z501,z1,z7,z3,z6])],[(0,[z41,z171,z2,z3,z4,z6]),(0,[z1,z7,z2,z16,z273,z6]),(0,[z49,z1,z7,z6,z27,z14]),(0,[z1,z7,z3,z4,z6,z1043])],[(0,[z894,z1,z2,z3,z4,z6]),(0,[z227,z49,z1,z7,z3,z6]),(0,[z1,z7,z2,z21,z271,z6]),(0,[z242,z1,z2,z3,z30,z6])],[(0,[z1,z7,z2,z4,z680,z14]),(0,[z49,z1,z7,z16,z107,z6])],[(0,[z1,z7,z1044,z3,z4,z6]),(0,[z1,z7,z2,z1045,z4,z6]),(0,[z1,z7,z2,z3,z1046,z6])],[(0,[z259,z1,z7,z3,z6,z31]),(0,[z1,z7,z2,z4,z6,z1047]),(0,[z49,z1,z7,z24,z3,z6]),(0,[z1,z7,z2,z3,z6,z767])],[(0,[z1,z7,z16,z204,z4,z6]),(0,[z1,z7,z11,z2,z190,z6])],[(0,[z1,z7,z1048,z3,z4,z6]),(0,[z1,z7,z2,z169,z4,z6]),(0,[z1,z7,z2,z1049,z4,z6]),(0,[z1,z7,z2,z866,z4,z6]),(0,[z1,z7,z2,z381,z184,z6]),(0,[z173,z1,z7,z2,z329,z31])],[(0,[z1,z7,z1050,z3,z4,z6]),(0,[z1,z7,z11,z2,z378,z6])],[(0,[z894,z42,z2,z3,z4,z6]),(0,[z1,z7,z2,z1051,z4,z6]),(0,[z1,z1052,z2,z3,z4,z6]),(0,[z1,z7,z2,z21,z273,z6]),(0,[z56,z1,z7,z11,z83,z6]),(0,[z1,z7,z2,z3,z6,z1053])]],
   [[(0,[z49,z1,z7,z2,z3,z6]),(1,[z7,z2,z963,z4,z6]),(0,[z1,z7,z2,z4,z6,z1054]),(0,[z1,z7,z2,z1055,z6,z14])],[(0,[z1,z7,z2,z3,z1056,z6]),(0,[z1,z7,z2,z4,z6,z1057]),(0,[z56,z49,z1,z7,z83,z6])],[(0,[z1058,z1,z2,z3,z4,z6]),(0,[z1,z7,z2,z4,z6,z1059]),(0,[z202,z1,z7,z3,z79,z6]),(0,[z264,z49,z1,z7,z3,z6]),(0,[z1,z7,z2,z6,z923,z14]),(0,[z1,z7,z2,z474,z6,z113]),(0,[z1,z7,z2,z1060,z4,z6])],[(0,[z468,z1,z195,z2,z3,z6])],[(0,[z898,z1,z7,z2,z3,z6]),(0,[z1,z7,z3,z762,z4,z6])],[(0,[z1,z2,z3,z800,z129,z6]),(0,[z1,z7,z2,z1061,z4,z6])],[(0,[z1,z7,z2,z3,z1062,z6]),(0,[z1,z1063,z2,z3,z4,z6])],[(0,[z1,z1064,z7,z2,z3,z6]),(0,[z272,z1,z11,z2,z3,z6]),(0,[z1,z7,z2,z3,z1065,z6]),(0,[z202,z1,z117,z3,z129,z6])],[(0,[z470,z42,z2,z3,z4,z6]),(0,[z63,z1,z195,z3,z4,z6]),(0,[z1,z522,z2,z3,z129,z6]),(0,[z223,z1,z2,z527,z4,z6])],[(0,[z49,z81,z1,z2,z123,z6]),(0,[z1,z7,z2,z3,z119,z6]),(0,[z82,z1,z2,z3,z4,z716])],[(0,[z1066,z1,z7,z3,z4,z6]),(0,[z1,z7,z11,z2,z244,z6]),(0,[z49,z611,z1,z7,z3,z6])],[(0,[z1,z7,z2,z3,z39,z31])],[(0,[z76,z1,z114,z7,z2,z6]),(0,[z49,z87,z7,z2,z132,z6]),(0,[z1,z7,z2,z4,z6,z1067])],[(0,[z1,z7,z1068,z2,z3,z6]),(0,[z1,z7,z2,z4,z1069,z6]),(0,[z1070,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z1071,z4,z6]),(0,[z1,z7,z2,z228,z4,z6]),(0,[z7,z2,z1072,z3,z4,z6]),(0,[z1,z7,z1073,z2,z3,z6])],[(0,[z54,z49,z1,z7,z3,z6]),(0,[z1,z7,z2,z1074,z4,z6]),(0,[z259,z111,z1,z7,z3,z6])]],
   [[(0,[z272,z2,z3,z4,z89,z6]),(0,[z49,z1,z7,z3,z6,z636]),(0,[z1075,z1,z7,z2,z3,z6]),(0,[z49,z1,z7,z162,z6,z14])],[(0,[z1,z7,z66,z2,z16,z6]),(0,[z183,z7,z350,z3,z4,z6]),(0,[z1,z7,z2,z4,z739,z6])],[(0,[z54,z49,z55,z7,z3,z6]),(0,[z1,z7,z2,z3,z1076,z6]),(0,[z87,z7,z2,z634,z4,z6]),(0,[z49,z1,z7,z234,z3,z6]),(0,[z81,z1,z2,z123,z273,z6]),(0,[z118,z7,z2,z381,z4,z6])],[(0,[z1,z7,z2,z1077,z4,z6]),(0,[z49,z1,z7,z463,z3,z6]),(1,[z746,z1,z7,z3,z6]),(0,[z1078,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z3,z1079,z6]),(0,[z988,z1,z7,z2,z4,z6]),(0,[z7,z2,z4,z6,z14,z1080])],[(0,[z1,z7,z1081,z2,z3,z6]),(0,[z1,z117,z3,z182,z129,z6]),(0,[z111,z1,z7,z2,z448,z6]),(0,[z49,z1,z7,z2,z3,z1082]),(0,[z1,z7,z2,z3,z52,z110])],[(0,[z1,z7,z552,z3,z184,z6]),(0,[z1,z1083,z2,z3,z4,z6])],[(0,[z1,z7,z2,z3,z4,z6]),(0,[z49,z155,z1,z7,z57,z6])],[(0,[z49,z225,z1,z7,z2,z6]),(0,[z1,z7,z2,z4,z6,z1084])],[(0,[z49,z1,z7,z3,z6,z188]),(0,[z56,z1,z7,z196,z4,z6]),(0,[z786,z87,z1,z7,z3,z6]),(0,[z1,z7,z2,z1085,z4,z6]),(0,[z1,z7,z1086,z2,z6,z14])],[(0,[z1,z7,z2,z1087,z3,z6]),(0,[z1,z7,z2,z3,z1088,z6])],[(0,[z49,z1,z7,z3,z601,z6]),(0,[z198,z1,z7,z2,z261,z6]),(0,[z1,z7,z3,z6,z1053,z27]),(0,[z96,z1,z7,z11,z3,z6]),(0,[z50,z1,z7,z2,z128,z6])],[(0,[z1,z7,z3,z848,z537,z6]),(0,[z47,z1,z7,z2,z3,z31]),(0,[z1,z7,z3,z4,z121,z880])],[(0,[z1,z7,z2,z16,z4,z366]),(0,[z1089,z7,z2,z3,z4,z6]),(0,[z1,z7,z1090,z350,z3,z6]),(0,[z1,z7,z2,z1091,z4,z6])],[(0,[z272,z1,z2,z3,z4,z6]),(0,[z1,z7,z34,z3,z4,z6])],[(0,[z1,z7,z2,z16,z4,z6]),(1,[z1,z7,z3,z738,z6]),(0,[z1,z7,z11,z2,z875,z6])],[(0,[z1,z7,z2,z3,z4,z1092]),(0,[z1,z7,z2,z4,z6,z1093]),(0,[z269,z7,z2,z79,z6,z14]),(0,[z1,z7,z2,z1094,z4,z6]),(0,[z1,z7,z2,z6,z180,z14])]],
   [[(0,[z1,z7,z2,z3,z4,z772]),(0,[z91,z7,z2,z4,z89,z14])],[(0,[z0,z183,z2,z3,z4,z6]),(0,[z1,z7,z2,z1095,z4,z6]),(0,[z111,z1,z7,z2,z739,z6]),(0,[z1,z7,z2,z3,z1096,z6])],[(0,[z54,z7,z9,z3,z4,z6]),(0,[z1,z7,z2,z1097,z4,z6]),(0,[z136,z49,z1,z7,z3,z27]),(0,[z1,z7,z2,z3,z1098,z6])],[(0,[z1,z7,z1099,z3,z4,z6]),(0,[z1,z7,z11,z2,z169,z6]),(0,[z49,z91,z7,z2,z3,z89]),(0,[z1,z7,z8,z3,z421,z121])],[(0,[z164,z41,z11,z2,z3,z6]),(0,[z1,z7,z228,z204,z4,z6]),(0,[z1100,z7,z2,z3,z4,z6]),(0,[z1,z7,z1101,z3,z4,z6])],[(0,[z87,z7,z2,z963,z4,z6]),(0,[z1,z7,z34,z16,z4,z6]),(0,[z272,z1,z2,z16,z4,z6]),(0,[z49,z1,z64,z7,z3,z6])],[(0,[z1,z7,z2,z1102,z4,z6]),(0,[z391,z1,z7,z66,z2,z6]),(0,[z70,z1,z7,z2,z4,z6]),(0,[z1,z7,z11,z2,z1103,z6])],[(0,[z73,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z16,z6]),(0,[z1,z7,z2,z128,z240,z6]),(0,[z1,z7,z2,z4,z6,z814])],[(0,[z1,z7,z2,z3,z1104,z6]),(0,[z1,z7,z2,z3,z6,z1105]),(0,[z1,z239,z2,z357,z4,z6]),(0,[z1,z7,z2,z4,z1106,z6]),(0,[z70,z1,z117,z2,z129,z6]),(0,[z1107,z7,z2,z3,z4,z6])],[(0,[z1,z7,z80,z3,z4,z6]),(0,[z1,z7,z2,z58,z52,z6]),(0,[z1,z7,z2,z1108,z4,z6])],[(0,[z1,z7,z1109,z3,z4,z6]),(0,[z54,z7,z9,z16,z4,z6]),(0,[z1,z7,z2,z3,z1110,z6]),(0,[z49,z1,z7,z3,z243,z6]),(0,[z1,z7,z2,z967,z4,z6]),(0,[z1,z7,z2,z3,z4,z1082]),(0,[z1,z7,z8,z3,z4,z295]),(0,[z1,z7,z1111,z2,z6,z14])],[(0,[z1,z7,z2,z3,z1112,z6]),(0,[z1113,z1,z7,z3,z4,z6]),(0,[z1114,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z2,z126,z6]),(0,[z802,z1,z7,z2,z4,z6])],[],[(0,[z1,z7,z2,z244,z4,z6]),(0,[z82,z183,z2,z3,z4,z25]),(0,[z49,z1,z7,z157,z3,z6]),(0,[z1,z7,z2,z4,z167,z14])],[(0,[z49,z7,z2,z3,z6,z364]),(0,[z1,z7,z2,z3,z738,z6]),(0,[z1,z7,z11,z3,z423,z6])],[(0,[z259,z1,z7,z11,z3,z6]),(0,[z73,z7,z2,z16,z4,z6]),(0,[z49,z374,z1,z7,z3,z6]),(0,[z1,z7,z134,z21,z4,z6])]],
   [[(0,[z1,z7,z11,z2,z832,z6]),(0,[z1,z7,z11,z2,z16,z14])],[(0,[z1,z7,z80,z16,z4,z6]),(0,[z63,z1,z109,z67,z4,z6])],[],[(0,[z1,z7,z2,z3,z1115,z6]),(0,[z50,z1,z7,z2,z6,z317])],[],[(0,[z1,z7,z2,z1116,z4,z6]),(0,[z1,z114,z7,z2,z6,z14]),(0,[z1,z7,z2,z1117,z4,z6])],[(0,[z54,z49,z1,z7,z16,z6]),(0,[z1,z7,z1118,z3,z4,z6]),(0,[z49,z1,z7,z3,z448,z6])],[(0,[z1,z7,z2,z4,z6,z1119]),(0,[z1,z7,z2,z142,z4,z6])],[(0,[z533,z49,z1,z7,z3,z6]),(0,[z85,z1,z7,z2,z4,z14]),(0,[z1,z2,z16,z784,z4,z6])],[(1,[z962,z1,z7,z3,z6]),(0,[z81,z1,z2,z123,z4,z6]),(0,[z73,z2,z3,z4,z5,z6]),(0,[z49,z1,z7,z230,z3,z6]),(0,[z49,z1,z1120,z2,z3,z6]),(0,[z1,z7,z3,z4,z685,z27])],[(0,[z164,z41,z2,z3,z4,z6]),(0,[z1,z1121,z2,z3,z4,z6]),(0,[z1,z7,z2,z277,z273,z6]),(0,[z1,z7,z2,z1122,z4,z6]),(0,[z1,z7,z265,z3,z21,z6])],[(0,[z1,z7,z2,z3,z1123,z6]),(0,[z49,z59,z1,z7,z3,z6]),(0,[z76,z1,z7,z11,z2,z6])],[(0,[z1,z7,z1124,z2,z3,z6]),(0,[z1,z7,z2,z238,z6,z14]),(0,[z1,z1125,z2,z3,z4,z6]),(1,[z7,z2,z3,z765,z6]),(0,[z7,z2,z3,z1126,z4,z6]),(0,[z1,z7,z350,z4,z6,z14]),(0,[z1,z7,z536,z20,z4,z6])],[(0,[z1,z7,z2,z3,z1127,z6]),(0,[z1,z7,z2,z43,z6,z14]),(0,[z840,z1,z7,z34,z3,z6]),(0,[z1,z2,z4,z6,z139,z14]),(0,[z1,z7,z1128,z2,z3,z6]),(0,[z1,z7,z2,z1129,z4,z6]),(0,[z1,z7,z57,z20,z71,z6])],[(0,[z1,z7,z2,z1130,z4,z6]),(0,[z1,z7,z2,z1131,z4,z6])],[(0,[z49,z1,z7,z2,z190,z6])]],
   [[(0,[z1,z7,z11,z552,z3,z6])],[(0,[z7,z2,z3,z4,z6,z364]),(0,[z1,z7,z1132,z3,z4,z6]),(0,[z1133,z1,z7,z2,z3,z6]),(0,[z7,z2,z3,z4,z6,z956]),(0,[z49,z1,z7,z2,z378,z6])],[(0,[z1,z7,z11,z283,z3,z6]),(0,[z1,z7,z2,z357,z304,z6]),(0,[z1,z7,z2,z1134,z4,z6])],[(0,[z1,z7,z2,z3,z6,z1135]),(0,[z49,z1,z7,z3,z95,z6]),(0,[z1,z7,z2,z3,z1136,z6]),(0,[z49,z879,z7,z2,z3,z6])],[(0,[z63,z1,z11,z67,z3,z6]),(0,[z49,z555,z1,z7,z3,z6]),(0,[z1137,z7,z2,z3,z4,z6]),(1,[z1,z2,z866,z4,z6]),(0,[z1,z7,z3,z1138,z273,z6]),(0,[z1,z7,z182,z4,z6,z14])],[(0,[z1,z7,z2,z3,z6,z1139]),(0,[z1,z7,z2,z249,z4,z14])],[(0,[z111,z1,z7,z2,z229,z6]),(0,[z1,z2,z713,z3,z4,z6]),(0,[z183,z7,z552,z3,z4,z6])],[(0,[z1,z7,z1140,z2,z3,z6]),(0,[z50,z1,z7,z2,z6,z331])],[(0,[z1,z7,z1141,z3,z4,z6]),(0,[z318,z1,z7,z2,z3,z31]),(0,[z202,z1,z7,z3,z4,z6]),(0,[z49,z1,z7,z3,z6,z110])],[(0,[z1,z7,z2,z4,z6,z1142]),(0,[z1143,z1,z7,z2,z4,z6]),(0,[z667,z7,z2,z90,z4,z6])],[(0,[z63,z1,z7,z133,z3,z6]),(0,[z700,z49,z1,z7,z3,z6]),(0,[z1,z124,z2,z4,z5,z148])],[(0,[z49,z1,z7,z2,z3,z1144])],[(0,[z0,z2,z3,z4,z175,z6]),(0,[z1,z7,z2,z58,z79,z6]),(0,[z49,z1,z64,z7,z16,z6])],[(0,[z155,z7,z2,z159,z4,z6]),(0,[z1,z171,z2,z357,z4,z6]),(0,[z1,z7,z2,z955,z4,z6]),(0,[z1,z7,z3,z1145,z4,z6]),(0,[z49,z1,z7,z2,z244,z6]),(0,[z1,z7,z11,z2,z1146,z6]),(1,[z1,z7,z2,z3,z767])],[(0,[z1,z7,z712,z2,z3,z6]),(0,[z1,z7,z1073,z552,z3,z6]),(0,[z49,z1,z7,z11,z240,z6]),(0,[z1,z7,z2,z908,z4,z6]),(0,[z1,z7,z2,z4,z12,z814])],[(0,[z0,z42,z2,z4,z6,z14]),(0,[z1,z7,z3,z4,z6,z948]),(0,[z1,z7,z1147,z3,z4,z6]),(0,[z1,z7,z3,z4,z6,z1148]),(0,[z72,z1,z7,z2,z3,z6])]],
   [[(0,[z1149,z1,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z1150,z6]),(0,[z202,z1,z7,z16,z4,z6]),(0,[z1,z2,z4,z6,z1040,z14]),(0,[z1,z7,z2,z1151,z4,z6])],[(0,[z962,z1,z7,z3,z4,z6]),(0,[z1,z7,z2,z1152,z4,z6]),(0,[z1,z7,z1153,z2,z3,z6]),(0,[z1,z7,z1154,z2,z3,z6]),(0,[z1155,z1,z7,z2,z6,z14])],[(0,[z1,z7,z1156,z3,z4,z6]),(0,[z1,z7,z2,z3,z1157,z6]),(0,[z18,z1,z7,z11,z3,z6]),(0,[z1,z7,z11,z58,z17,z6])],[(0,[z1,z7,z2,z3,z4,z1158])],[(0,[z1,z7,z2,z3,z1159,z6]),(0,[z1,z7,z2,z16,z119,z6])],[(0,[z111,z1,z7,z2,z271,z6]),(0,[z1,z7,z83,z690,z4,z6]),(0,[z1,z7,z128,z134,z21,z6])],[(0,[z1,z7,z1160,z3,z4,z6]),(0,[z1,z7,z2,z3,z52,z767])],[(0,[z1,z2,z3,z4,z6,z1161])],[(0,[z1,z1162,z2,z3,z4,z6]),(0,[z49,z1,z7,z105,z3,z6]),(0,[z49,z1,z7,z328,z3,z6]),(0,[z1,z7,z2,z190,z6,z303]),(0,[z1,z7,z1163,z3,z4,z6]),(0,[z173,z1,z7,z2,z192,z31])],[(0,[z1,z7,z2,z3,z4,z1164]),(0,[z1,z7,z2,z1165,z4,z6]),(0,[z82,z1,z11,z2,z3,z25]),(0,[z49,z1,z7,z3,z370,z6])],[(0,[z1,z7,z1166,z2,z3,z6]),(0,[z1,z7,z2,z1103,z4,z6])],[(0,[z54,z76,z7,z9,z4,z6]),(0,[z431,z202,z1,z7,z3,z6]),(0,[z49,z73,z7,z2,z3,z6]),(0,[z1,z7,z3,z6,z180,z158]),(0,[z1,z7,z265,z3,z52,z6])],[(0,[z1,z7,z2,z4,z6,z1167]),(0,[z1168,z1,z2,z3,z4,z6]),(0,[z1,z7,z2,z1169,z4,z6]),(0,[z111,z1,z7,z2,z273,z6])],[(0,[z1,z124,z2,z4,z5,z14]),(0,[z1,z7,z1086,z2,z3,z6]),(0,[z1,z7,z2,z378,z174,z52])],[(0,[z1,z7,z11,z240,z17,z6])],[(1,[z894,z2,z3,z4,z6]),(0,[z232,z7,z2,z19,z6,z14]),(0,[z49,z202,z1,z7,z3,z6]),(0,[z1,z1120,z2,z3,z4,z6])]],
   [[(0,[z49,z1,z7,z323,z3,z6]),(0,[z1,z7,z2,z3,z800,z6]),(0,[z1,z7,z11,z2,z1025,z6])],[(0,[z1,z7,z2,z4,z6,z1170]),(0,[z1,z7,z1171,z3,z4,z6]),(0,[z35,z50,z1,z7,z2,z6]),(0,[z1,z7,z2,z277,z4,z6]),(0,[z1,z7,z2,z3,z4,z1144]),(1,[z1,z7,z720,z6,z14])],[(0,[z1,z7,z1172,z3,z4,z6]),(0,[z49,z1,z7,z3,z208,z6]),(0,[z1,z7,z265,z3,z19,z6]),(0,[z1,z7,z2,z1146,z4,z6]),(0,[z191,z1,z2,z547,z4,z6])],[(0,[z1,z64,z7,z133,z3,z6]),(0,[z1,z7,z2,z244,z119,z6]),(0,[z1,z124,z2,z3,z4,z716]),(0,[z56,z1,z7,z107,z4,z6])],[(0,[z0,z42,z2,z3,z224,z6]),(0,[z155,z312,z7,z2,z4,z6]),(0,[z1,z7,z1173,z3,z4,z6]),(0,[z49,z1,z7,z2,z1174,z6]),(0,[z1,z7,z11,z2,z6,z1175])],[(0,[z1,z7,z2,z16,z4,z694]),(0,[z49,z1,z7,z674,z3,z6]),(0,[z411,z1,z7,z107,z4,z6])],[(0,[z49,z1,z7,z2,z169,z6]),(0,[z1,z7,z1090,z2,z3,z6]),(0,[z1,z7,z265,z4,z6,z14])],[(0,[z272,z42,z2,z3,z4,z6]),(0,[z1,z7,z1176,z2,z3,z6]),(0,[z1,z7,z11,z2,z109,z6]),(0,[z1,z7,z2,z1177,z4,z6]),(0,[z1,z7,z3,z4,z6,z1178])],[(0,[z1,z7,z2,z294,z4,z6])],[(0,[z1,z7,z2,z109,z4,z6]),(0,[z1,z7,z2,z6,z921,z14])],[(0,[z50,z1,z7,z2,z83,z6]),(0,[z1,z7,z2,z16,z4,z14])],[(0,[z164,z2,z3,z4,z6,z395]),(0,[z111,z1,z7,z2,z322,z6]),(0,[z1,z7,z2,z808,z4,z6]),(0,[z1,z7,z3,z1138,z4,z6]),(0,[z49,z1,z7,z3,z6,z27])],[(0,[z225,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z16,z4,z15]),(0,[z1,z7,z2,z16,z1096,z6])],[(0,[z88,z239,z2,z3,z4,z156])],[(0,[z1,z662,z2,z3,z129,z6]),(0,[z88,z272,z2,z3,z4,z156]),(0,[z1,z7,z2,z3,z787,z6]),(0,[z81,z1,z2,z866,z4,z6]),(0,[z1,z7,z2,z3,z84,z6]),(0,[z1,z7,z57,z261,z4,z6]),(0,[z431,z1,z2,z302,z3,z6]),(0,[z1,z7,z2,z708,z4,z6])],[(0,[z1,z7,z2,z4,z6,z1179]),(0,[z35,z1,z11,z2,z69,z6]),(0,[z1,z7,z11,z2,z1129,z6])]],
   [[(0,[z49,z35,z1,z2,z69,z6]),(0,[z35,z1,z482,z2,z4,z6])],[(0,[z388,z7,z2,z3,z4,z156]),(0,[z63,z1,z66,z67,z3,z6]),(0,[z183,z7,z2,z381,z4,z6]),(0,[z1,z7,z552,z4,z6,z14]),(0,[z1,z7,z240,z17,z4,z6]),(0,[z1,z7,z2,z4,z6,z1180])],[(0,[z49,z0,z42,z2,z3,z6]),(0,[z1,z7,z2,z1181,z4,z6]),(0,[z50,z1,z7,z2,z329,z6]),(0,[z173,z1,z7,z2,z3,z31])],[(0,[z1,z7,z2,z1182,z4,z6]),(0,[z1,z7,z2,z3,z1183,z6]),(0,[z49,z1,z7,z2,z16,z14])],[(0,[z1,z7,z2,z3,z1184,z6]),(0,[z118,z7,z2,z3,z184,z6]),(0,[z56,z1,z7,z777,z4,z6]),(0,[z112,z1,z7,z83,z4,z6]),(0,[z49,z1,z7,z8,z6,z14])],[(0,[z1,z7,z2,z1185,z4,z6]),(0,[z1,z7,z2,z3,z1186,z6]),(0,[z22,z7,z2,z4,z6,z275])],[(0,[z1,z7,z11,z2,z414,z6]),(0,[z72,z1,z7,z2,z16,z6])],[(0,[z54,z114,z7,z9,z3,z6]),(0,[z1187,z7,z2,z3,z4,z6]),(0,[z1,z7,z2,z3,z745,z6])],[(0,[z49,z492,z1,z7,z3,z6]),(0,[z1,z117,z2,z3,z129,z6]),(0,[z49,z1,z7,z260,z3,z6]),(0,[z438,z1,z443,z2,z3,z6])],[(0,[z1188,z1,z7,z3,z4,z6]),(0,[z49,z1,z7,z38,z3,z6]),(0,[z1,z7,z290,z2,z58,z6])],[(0,[z1,z114,z7,z2,z3,z6]),(0,[z1,z7,z2,z4,z6,z1189]),(0,[z1,z7,z2,z3,z1190,z6]),(0,[z1,z7,z11,z3,z738,z6])],[(0,[z49,z1,z7,z559,z3,z6]),(0,[z85,z1,z7,z2,z113,z14])],[(0,[z63,z49,z1,z443,z3,z6]),(0,[z1,z7,z11,z265,z3,z6])],[(0,[z1,z7,z2,z1191,z3,z4])],[(0,[z1,z7,z2,z4,z6,z426]),(0,[z1,z7,z265,z3,z79,z6]),(0,[z1,z7,z2,z357,z247,z6]),(0,[z1,z7,z1192,z3,z4,z6]),(0,[z1193,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z21,z84,z6])],[(0,[z1,z1194,z2,z3,z4,z6]),(0,[z1,z7,z3,z1195,z4,z6]),(0,[z1,z7,z2,z4,z358,z14]),(0,[z1,z7,z2,z3,z1196,z6]),(0,[z1,z7,z3,z17,z738,z6]),(0,[z1,z7,z11,z3,z134,z6])]],
   [[(0,[z1,z117,z2,z16,z129,z6])],[(0,[z1,z7,z11,z2,z6,z426])],[(0,[z1,z1197,z2,z3,z4,z6]),(0,[z1022,z7,z2,z3,z4,z6]),(0,[z1,z7,z3,z448,z17,z6]),(0,[z1,z7,z1198,z3,z4,z6])],[(0,[z1,z7,z2,z101,z6,z14]),(0,[z49,z1,z7,z552,z3,z6]),(0,[z49,z1,z7,z3,z6,z299])],[(0,[z1,z7,z2,z1199,z4,z6]),(0,[z1200,z1,z7,z4,z6,z14])],[(0,[z164,z41,z2,z16,z4,z6]),(0,[z402,z1,z2,z3,z30,z6]),(0,[z49,z1201,z7,z2,z3,z6])],[(0,[z1,z7,z2,z3,z1202,z6]),(0,[z1,z7,z2,z1203,z4,z6])],[(0,[z1,z7,z2,z3,z1204,z6]),(0,[z88,z7,z2,z3,z304,z156]),(0,[z49,z256,z1,z7,z3,z6]),(0,[z1,z7,z2,z190,z421,z6]),(0,[z1,z7,z2,z877,z6,z14])],[(0,[z54,z49,z7,z9,z3,z6]),(0,[z259,z269,z7,z3,z79,z6]),(0,[z1,z7,z11,z2,z885,z6]),(0,[z50,z1,z7,z2,z6,z113])],[(0,[z155,z50,z1,z7,z2,z6]),(0,[z1,z64,z140,z3,z243,z6]),(0,[z1,z124,z2,z93,z4,z5]),(0,[z1,z7,z2,z3,z1205,z6]),(0,[z1,z7,z720,z6,z113,z14])],[(0,[z460,z49,z1,z7,z3,z6]),(0,[z1,z7,z1198,z16,z4,z6])],[],[(0,[z1,z7,z1206,z3,z4,z6]),(0,[z49,z1,z7,z674,z16,z6]),(0,[z1,z7,z2,z1207,z142,z6])],[(0,[z49,z1,z7,z3,z207,z6]),(0,[z7,z13,z804,z3,z4,z6]),(0,[z315,z202,z1,z7,z3,z6]),(0,[z1,z7,z2,z4,z295,z14]),(0,[z1,z7,z4,z6,z14,z813])],[(0,[z49,z1,z7,z3,z508,z6]),(0,[z1,z7,z2,z976,z4,z6]),(0,[z49,z1,z7,z3,z6,z1053])],[(0,[z1,z7,z3,z4,z1208,z6]),(0,[z1,z7,z2,z1209,z4,z6])]],
   [[(0,[z651,z7,z2,z3,z19,z6]),(0,[z1,z7,z133,z2,z6,z14]),(0,[z1,z117,z2,z3,z800,z6]),(0,[z183,z7,z2,z3,z184,z6])],[(0,[z1,z838,z2,z3,z4,z6]),(0,[z1,z7,z11,z2,z240,z6]),(0,[z1,z7,z2,z1210,z4,z6])],[(0,[z88,z171,z2,z3,z4,z156]),(0,[z1,z7,z2,z3,z1211,z6]),(0,[z1,z7,z2,z58,z4,z6]),(1,[z1,z7,z2,z4,z814]),(0,[z1,z7,z37,z4,z6,z53])],[(0,[z87,z7,z2,z132,z271,z6]),(0,[z269,z7,z3,z204,z79,z6]),(0,[z202,z1,z7,z277,z4,z6])],[(0,[z850,z1,z7,z2,z3,z6]),(0,[z1,z7,z66,z2,z109,z6]),(0,[z168,z199,z7,z2,z3,z6])],[(0,[z1,z7,z1212,z3,z4,z6]),(0,[z91,z171,z2,z3,z4,z6]),(0,[z1,z7,z11,z2,z1102,z6])],[(0,[z1,z7,z57,z615,z4,z6]),(0,[z1155,z1,z7,z2,z3,z6]),(0,[z1,z7,z11,z2,z16,z12])],[(0,[z1,z7,z2,z3,z537,z6]),(0,[z0,z42,z11,z2,z3,z6]),(0,[z259,z1,z7,z128,z3,z6]),(0,[z1213,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z3,z783,z6]),(0,[z136,z1,z7,z3,z180,z27])],[(0,[z7,z2,z3,z963,z4,z6]),(0,[z7,z2,z3,z765,z79,z6]),(0,[z1,z7,z2,z3,z210,z6]),(0,[z1,z7,z1214,z3,z4,z6])],[(0,[z1,z7,z2,z744,z4,z6]),(0,[z1,z7,z2,z4,z6,z1215]),(0,[z1,z7,z2,z1216,z4,z6]),(0,[z111,z1,z7,z2,z599,z6]),(0,[z707,z1,z7,z2,z6,z148])],[(0,[z1,z7,z350,z3,z4,z6])],[(0,[z49,z1,z7,z503,z3,z6]),(0,[z1,z7,z230,z2,z58,z6]),(0,[z1,z7,z2,z3,z52,z642]),(0,[z1,z7,z1217,z2,z3,z6])],[(0,[z49,z1,z456,z7,z3,z6]),(0,[z1,z7,z11,z3,z204,z6])],[(0,[z1218,z1,z7,z2,z4,z6]),(0,[z1,z1219,z2,z3,z4,z6]),(0,[z49,z1,z7,z3,z379,z6]),(0,[z1,z7,z2,z3,z1220,z6]),(0,[z1,z7,z8,z3,z4,z121]),(0,[z1,z7,z37,z128,z3,z6])],[(0,[z225,z1,z7,z2,z129,z6]),(0,[z1,z7,z2,z4,z6,z1221]),(0,[z1,z7,z2,z240,z4,z6]),(0,[z1,z7,z2,z3,z1222,z6]),(0,[z1223,z1,z7,z2,z6,z14])],[(0,[z1,z7,z2,z16,z537,z6]),(0,[z1,z7,z2,z937,z43,z6]),(0,[z155,z7,z2,z90,z4,z6]),(0,[z816,z7,z2,z3,z4,z6]),(0,[z1,z7,z720,z2,z6,z14])]],
   [[(0,[z315,z1,z2,z302,z3,z6])],[(0,[z1,z114,z7,z2,z16,z6])],[(0,[z1,z7,z2,z3,z1224,z6]),(0,[z1,z7,z2,z1225,z4,z6]),(0,[z1,z7,z11,z2,z1074,z6]),(0,[z50,z1,z7,z2,z6,z14])],[(0,[z1,z7,z2,z1226,z4,z6]),(0,[z49,z1,z7,z425,z3,z6]),(0,[z202,z1,z7,z3,z174,z6])],[(0,[z63,z391,z1,z67,z4,z6]),(0,[z1,z7,z1227,z3,z4,z6]),(0,[z1228,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z4,z6,z1175]),(0,[z1,z7,z16,z134,z4,z6])],[(0,[z1,z7,z2,z1229,z3,z6]),(0,[z1,z7,z8,z3,z4,z254]),(0,[z608,z1,z2,z3,z30,z6]),(0,[z255,z1,z7,z3,z4,z27]),(0,[z82,z1,z2,z3,z119,z25]),(0,[z1,z7,z8,z16,z4,z121])],[(0,[z1,z7,z2,z1230,z4,z6]),(0,[z1,z7,z11,z34,z3,z6]),(0,[z1,z64,z140,z4,z6,z14]),(0,[z1,z7,z2,z6,z113,z53])],[(0,[z1,z1231,z2,z3,z4,z6]),(0,[z1,z7,z3,z4,z6,z1232]),(1,[z1,z2,z3,z800,z6]),(0,[z85,z1,z7,z2,z4,z814])],[(0,[z388,z0,z2,z3,z4,z6]),(0,[z1,z7,z1233,z80,z3,z6]),(0,[z1234,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z84,z6,z14]),(0,[z1,z7,z2,z71,z6,z14]),(0,[z825,z1,z7,z4,z6,z14])],[(0,[z1,z7,z2,z3,z1235,z6]),(0,[z1,z7,z11,z2,z1177,z6])],[(0,[z49,z1,z7,z2,z109,z6])],[(0,[z1,z7,z2,z3,z6,z1236]),(0,[z49,z1,z1083,z2,z3,z6])],[(0,[z1237,z1,z7,z80,z3,z6]),(0,[z88,z272,z2,z3,z4,z6]),(0,[z1,z7,z2,z4,z6,z1238]),(0,[z1239,z1,z7,z2,z4,z6]),(0,[z49,z1,z7,z3,z406,z6])],[(0,[z1,z7,z2,z1240,z4,z6]),(0,[z1,z7,z2,z16,z113,z14])],[(0,[z1241,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z3,z4,z716])],[(0,[z1,z7,z2,z448,z240,z6])]],
   [[(0,[z91,z7,z2,z3,z4,z226]),(0,[z1,z2,z3,z1242,z4,z6]),(0,[z88,z7,z2,z414,z4,z156]),(0,[z1243,z1,z7,z2,z3,z6]),(0,[z49,z1,z7,z3,z6,z416]),(0,[z1,z7,z2,z1244,z4,z6])],[(0,[z1,z7,z1245,z3,z4,z6])],[(0,[z1,z7,z2,z4,z524,z14]),(0,[z1,z7,z11,z2,z357,z6]),(0,[z1,z7,z1111,z2,z3,z6]),(0,[z82,z1,z2,z3,z4,z25]),(0,[z49,z826,z1,z7,z2,z6]),(0,[z1,z1024,z2,z3,z4,z6])],[(0,[z801,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z3,z6,z1246]),(0,[z1,z7,z2,z4,z6,z1247]),(0,[z1248,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z3,z852,z6])],[(0,[z7,z2,z3,z993,z4,z6])],[(0,[z55,z7,z13,z3,z101,z6]),(0,[z1,z7,z2,z357,z4,z6])],[(0,[z1,z7,z2,z1249,z4,z6]),(0,[z49,z1,z7,z16,z6,z27]),(0,[z1,z7,z6,z113,z14,z769])],[(0,[z7,z2,z132,z963,z4,z6]),(0,[z1,z7,z1250,z2,z3,z6]),(0,[z1,z7,z2,z3,z174,z295])],[(0,[z1,z7,z2,z3,z1251,z6]),(0,[z41,z2,z3,z4,z6,z510]),(0,[z1,z7,z2,z4,z6,z1252]),(0,[z1,z7,z2,z1174,z4,z6])],[(0,[z49,z137,z1,z7,z3,z6]),(0,[z1253,z1,z7,z2,z3,z4]),(0,[z259,z1,z7,z4,z6,z14]),(0,[z49,z1,z7,z2,z414,z6]),(0,[z49,z391,z1,z7,z2,z6]),(0,[z1,z7,z2,z16,z84,z6]),(0,[z1,z7,z2,z4,z6,z1254])],[(0,[z49,z1,z7,z507,z3,z6]),(0,[z82,z1,z2,z16,z4,z25])],[(0,[z894,z0,z2,z3,z4,z6]),(0,[z49,z55,z1,z7,z6,z14]),(0,[z49,z1,z7,z3,z6,z598]),(0,[z1,z7,z57,z777,z4,z6]),(0,[z1,z7,z3,z4,z880,z27])],[(0,[z1,z7,z1255,z2,z3,z6]),(0,[z1,z7,z34,z357,z4,z6]),(0,[z111,z1,z7,z2,z340,z6]),(0,[z1,z7,z37,z3,z174,z52])],[(0,[z1,z7,z2,z1256,z4,z6]),(0,[z1,z7,z2,z929,z4,z6]),(0,[z49,z1,z7,z3,z738,z6])],[(0,[z1,z7,z2,z3,z1257,z6]),(0,[z7,z2,z3,z4,z772,z156]),(0,[z1,z7,z2,z3,z743,z6]),(0,[z1258,z1,z7,z2,z4,z6]),(0,[z1,z7,z11,z37,z3,z6]),(1,[z1,z7,z2,z6,z725]),(0,[z1,z7,z2,z1259,z4,z6]),(0,[z1,z7,z2,z378,z4,z6])],[(0,[z1,z1260,z2,z3,z4,z6]),(0,[z1,z7,z1261,z3,z4,z6]),(0,[z49,z1,z7,z265,z3,z6]),(0,[z1,z7,z37,z4,z6,z14]),(0,[z1,z7,z2,z3,z4,z767])]],
   [[(0,[z49,z1,z7,z518,z3,z6]),(0,[z1,z7,z2,z3,z1262,z6]),(0,[z1,z7,z1263,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z716]),(0,[z1,z7,z2,z1264,z4,z6])],[(0,[z1,z2,z3,z4,z6,z1265]),(0,[z87,z7,z2,z132,z4,z6]),(0,[z1,z7,z2,z1266,z4,z6]),(0,[z1,z7,z3,z1267,z4,z6]),(0,[z1,z7,z16,z4,z6,z158])],[(0,[z1,z7,z1268,z3,z4,z6]),(0,[z894,z7,z2,z3,z4,z6]),(0,[z1,z7,z16,z182,z4,z6]),(0,[z1,z7,z552,z3,z119,z6]),(0,[z49,z1,z7,z57,z83,z6]),(0,[z49,z1,z7,z3,z134,z6])],[(0,[z1,z7,z2,z4,z566,z14]),(0,[z88,z7,z2,z3,z247,z156]),(0,[z1,z117,z2,z277,z129,z6]),(0,[z49,z1,z7,z536,z3,z6])],[(0,[z91,z7,z2,z3,z4,z772]),(0,[z49,z1,z7,z2,z6,z426]),(0,[z1,z7,z2,z58,z129,z6]),(0,[z1,z7,z265,z3,z4,z6]),(0,[z7,z2,z3,z4,z6,z1080]),(0,[z49,z1,z1162,z2,z3,z6])],[(0,[z521,z49,z1,z7,z3,z6]),(0,[z1,z7,z1269,z2,z3,z6]),(0,[z49,z81,z1,z7,z57,z6])],[],[(0,[z1,z7,z2,z3,z1270,z6]),(0,[z225,z1,z7,z2,z30,z6])],[(0,[z1,z7,z2,z1271,z4,z6]),(0,[z1,z7,z80,z357,z4,z6]),(0,[z49,z684,z1,z7,z3,z6])],[(0,[z1,z7,z1272,z2,z3,z6]),(0,[z82,z1,z2,z244,z4,z25]),(0,[z1,z7,z3,z421,z6,z27])],[(0,[z1,z7,z2,z3,z1273,z6]),(0,[z1201,z7,z2,z3,z4,z6])],[],[(0,[z1,z7,z2,z1274,z4,z6]),(0,[z1,z7,z3,z4,z6,z1275]),(0,[z1,z7,z1276,z3,z4,z6])],[(0,[z1,z7,z2,z3,z135,z6]),(0,[z1277,z7,z2,z3,z4,z6]),(0,[z49,z1,z7,z692,z3,z6]),(0,[z1,z7,z2,z1207,z3,z6])],[(0,[z7,z2,z804,z3,z4,z6]),(0,[z1,z7,z2,z1278,z4,z6]),(0,[z1,z7,z2,z128,z228,z6]),(0,[z1,z7,z720,z3,z6,z14])],[(0,[z1279,z1,z7,z2,z4,z6]),(0,[z1,z7,z552,z3,z4,z6]),(0,[z1,z7,z2,z1280,z4,z6]),(0,[z746,z1,z7,z2,z3,z6]),(0,[z49,z1,z7,z3,z496,z6]),(0,[z494,z1,z7,z2,z4,z14])]],
   [[(0,[z118,z7,z2,z4,z6,z14]),(0,[z1,z7,z350,z3,z119,z6]),(0,[z1,z7,z2,z16,z4,z12])],[(0,[z1,z7,z1281,z3,z4,z6]),(0,[z1,z7,z2,z1282,z3,z6]),(0,[z49,z1,z7,z3,z491,z6]),(0,[z1,z7,z2,z3,z4,z814])],[(0,[z962,z1,z7,z3,z537,z6]),(0,[z49,z1,z7,z461,z3,z6]),(0,[z1,z7,z2,z415,z58,z6])],[(0,[z1,z239,z2,z3,z304,z6]),(0,[z1283,z1,z7,z2,z3,z6]),(1,[z1,z7,z777,z4,z6]),(0,[z49,z1,z7,z2,z295,z14]),(0,[z1,z7,z2,z6,z113,z14])],[(0,[z1,z7,z2,z1284,z4,z6]),(0,[z1,z7,z2,z1285,z4,z6]),(0,[z49,z1,z7,z2,z240,z6]),(0,[z1286,z1,z7,z2,z3,z6]),(0,[z1,z7,z4,z6,z158,z53])],[(0,[z1,z7,z133,z2,z3,z6]),(0,[z1,z7,z2,z3,z1287,z6]),(0,[z1,z7,z2,z128,z277,z6])],[(0,[z1,z7,z1288,z3,z4,z6]),(0,[z1,z7,z1233,z2,z3,z6])],[(0,[z1,z7,z2,z3,z1289,z6]),(0,[z337,z1,z7,z3,z4,z27]),(0,[z754,z1,z7,z2,z243,z6]),(0,[z1213,z1,z7,z552,z3,z6]),(0,[z1,z7,z552,z16,z4,z6]),(0,[z1,z7,z2,z184,z6,z14]),(0,[z1,z2,z4,z6,z14,z916]),(0,[z726,z1,z7,z2,z3,z6])],[(0,[z1,z7,z2,z3,z1290,z6]),(0,[z141,z1,z7,z83,z4,z6])],[(0,[z1,z7,z2,z1291,z4,z6]),(0,[z1,z7,z2,z1292,z4,z6]),(0,[z49,z1,z7,z181,z6,z14]),(0,[z49,z1,z7,z2,z16,z12]),(0,[z1,z7,z2,z16,z4,z814])],[(0,[z1,z7,z1293,z2,z3,z6]),(0,[z1237,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z3,z1294,z6]),(0,[z1295,z1,z7,z2,z3,z6])],[(0,[z1,z7,z1296,z3,z4,z6]),(0,[z391,z1,z7,z11,z2,z6]),(0,[z49,z505,z1,z7,z3,z6])],[(0,[z173,z1,z7,z2,z16,z31])],[(0,[z63,z49,z1,z64,z3,z6])],[(0,[z1,z7,z2,z1297,z4,z6]),(0,[z1,z7,z2,z4,z6,z917])],[(0,[z1,z7,z2,z3,z1298,z6]),(0,[z49,z1,z7,z3,z204,z6]),(0,[z1,z7,z2,z1299,z4,z6])]],
   [[(0,[z1,z114,z7,z2,z169,z6]),(0,[z1028,z1,z7,z2,z4,z6]),(0,[z1,z7,z2,z1300,z4,z6]),(0,[z49,z1003,z7,z2,z3,z6]),(0,[z49,z1,z7,z3,z538,z6])],[(0,[z1,z7,z2,z1301,z4,z6]),(0,[z1,z7,z2,z4,z6,z1302]),(0,[z1,z2,z1303,z3,z4,z6]),(0,[z1,z7,z2,z3,z1304,z6]),(0,[z1305,z1,z7,z2,z3,z6]),(0,[z49,z1,z7,z3,z632,z6]),(0,[z111,z1,z7,z2,z240,z6]),(0,[z1,z7,z2,z128,z6,z53])],[(0,[z1,z7,z2,z3,z1306,z6]),(0,[z1200,z1,z7,z3,z4,z6]),(0,[z785,z7,z2,z3,z4,z6])],[(0,[z49,z1,z7,z196,z3,z6]),(0,[z7,z2,z3,z4,z89,z772]),(0,[z1,z7,z2,z4,z6,z1307]),(0,[z1,z7,z2,z16,z210,z6]),(0,[z1,z7,z2,z777,z4,z6]),(0,[z1223,z1,z7,z2,z3,z6])],[(0,[z88,z7,z11,z2,z3,z156]),(0,[z49,z1,z7,z3,z584,z6]),(0,[z223,z1,z2,z123,z4,z6])],[(0,[z1,z114,z7,z3,z6,z27]),(0,[z1,z7,z350,z16,z4,z6])],[(0,[z1,z7,z2,z3,z1308,z6]),(0,[z49,z1,z7,z3,z6,z549]),(0,[z1,z7,z2,z1309,z4,z6]),(0,[z1,z7,z2,z3,z6,z882]),(0,[z1,z7,z552,z244,z4,z6]),(0,[z136,z1,z7,z142,z4,z27])],[(0,[z1,z7,z2,z3,z1310,z6]),(0,[z50,z1,z7,z2,z3,z6]),(0,[z1,z7,z2,z3,z1055,z6])],[(0,[z55,z7,z13,z3,z43,z6]),(0,[z1,z239,z2,z4,z6,z14]),(0,[z1,z7,z3,z783,z83,z6]),(0,[z1,z7,z2,z6,z725,z14])],[(0,[z49,z1,z7,z34,z3,z6]),(0,[z1,z7,z2,z1311,z3,z6]),(0,[z202,z1,z7,z3,z6,z31]),(1,[z1,z7,z720,z3,z6])],[(0,[z1,z7,z11,z2,z93,z6]),(0,[z1,z7,z2,z6,z14,z766])],[(0,[z1,z7,z2,z3,z1312,z6]),(0,[z1,z7,z1313,z2,z3,z6]),(0,[z793,z7,z2,z3,z4,z6])],[(0,[z1,z7,z2,z3,z101,z6]),(0,[z1,z7,z3,z204,z4,z6]),(0,[z1,z2,z3,z4,z6,z1314]),(0,[z91,z7,z11,z2,z3,z89])],[(0,[z1,z7,z3,z4,z1315,z6]),(0,[z1,z7,z2,z58,z30,z6]),(0,[z1,z7,z2,z381,z119,z6])],[(0,[z111,z1,z7,z2,z62,z6])],[(0,[z1,z7,z2,z963,z4,z6]),(0,[z1316,z7,z2,z3,z4,z6]),(0,[z56,z1,z7,z448,z83,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 499) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 499).take 497) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 996).take 418) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1414)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [499, 497, 418] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 136).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 136).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 253).take 138).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 391).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [136, 117, 138, 121] = true :=
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

end PEqualNP.Outside.L_meta_38699

theorem PEqualNP.Outside.L_meta_38699 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4272597504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4272597504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38699.solve