import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46060

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
  Nat.testBit (4277074602 * 2 ^ 32 + 4242589824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0442412b8c4386c9#64 ++ 0x00110904ae310e1b#64 ++ 0x0cc647ff8c478ffe#64 ++ 0x9433191ffe311e3f#64 : BitVec 256),
   (0x1159849805d83b52#64 ++ 0x08456612601760ed#64 ++ 0x337984980ff8fffd#64 ++ 0xe8cde612603fe3ff#64 : BitVec 256),
   (0x4380d8e0b02dd19c#64 ++ 0x050e036382c0b746#64 ++ 0xc381f8e1f07ff1fb#64 ++ 0xbf0e07e387c1ffc7#64 : BitVec 256),
   (0xbc016f01da80ec20#64 ++ 0x12f005bc076a03b0#64 ++ 0xfc01ff01ff80fe37#64 ++ 0xdff007fc07fe03f8#64 : BitVec 256),
   (0xeeee00016f760000#64 ++ 0x23bbb80005bdd800#64 ++ 0xfffe0001ffff002f#64 ++ 0xeffff80007fffc00#64 : BitVec 256),
   (0xfbb5b6d400000000#64 ++ 0x03eed6db50000000#64 ++ 0xfffffffe0000001f#64 ++ 0xf3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc647ff8c478ffe 0x9433191ffe311e3f

def z1 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x337984980ff8fffd 0xe8cde612603fe3ff

def z2 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc381f861f03f7003 0x3f0e07e187c0fdc0

def z3 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc381f8e1f07ff1fb 0xbf0e07e387c1ffc7

def z4 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01ff01ff80fe37 0xdff007fc07fe03f8

def z5 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe0001ffff002f 0xeffff80007fffc00

def z6 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfffffffe0000001f 0xf3fffffff8000000

def z7 : W := mkw 0x0040000804400240 0x0001000020110009 0x004004980c408ffc 0x800100126031023f

def z8 : W := mkw 0x155bc5bb8ddbbfdb 0x08556f16ee376eff 0x3fffc7ff8fffffff 0xfcffff1ffe3fffff

def z9 : W := mkw 0xfbb5fef4b025c08c 0x07eed7fbd2c09702 0xfffffffff007001f 0xf7ffffffffc01c00

def z10 : W := mkw 0x5381dce0b0adf99c 0x054e077382c2b7e6 0xf381fce1ffffffff 0xffce07f387ffffff

def z11 : W := mkw 0xeaec000005500000 0x03abb00000154000 0xfffe00000ff8002f 0xebfff800003fe000

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000001f0000023 0x8f00000007c00000

def z13 : W := mkw 0x00004820b02dd19c 0x0400012082c0b746 0x00000001f07ff1e0 0x0c00000007c1ffc7

def z14 : W := mkw 0xfbb5fef4b02dd19c 0x07eed7fbd2c0b746 0xfffffffff07ff1ff 0xffffffffffc1ffc7

def z15 : W := mkw 0x0002002200030089 0x0000080088000c02 0x0086006600070000 0x0002180198001c00

def z16 : W := mkw 0x1111849000883912 0x08444612400220e4 0x0001800000007000 0x00000600000001c0

def z17 : W := mkw 0x044200010c420000 0x0011080004310800 0x0cc600018c47002e 0x8433180006311c00

def z18 : W := mkw 0xeeee412bef7786c9 0x23bbb904afbdde1b 0xfffe47ffffff8fff 0xfffff91ffffffe3f

def z19 : W := mkw 0xbc5927194fd02e62 0x1af1649c653f40b9 0x3c7807180f800e04 0x40f1e01c603e0038

def z20 : W := mkw 0x004a000025760000 0x200128000095d800 0x00000000007f0000 0x000000000001fc00

def z21 : W := mkw 0xb801260000000000 0x02e0049800000000 0xfc01ff0000000017 0xd3f007fc00000000

def z22 : W := mkw 0xffb5ffd5da80ec20 0x13fed7ff576a03b0 0xffffffffff80fe3f 0xfffffffffffe03f8

def z23 : W := mkw 0xeeee00096f760240 0x23bbb80025bdd809 0xfffe0499ffff8fff 0xeffff81267fffe3f

def z24 : W := mkw 0x1111849000000000 0x0044461240000000 0x337984980000001d 0xe0cde61260000000

def z25 : W := mkw 0xfbfdb6dc05d83b52 0x0beff6db701760ed 0xfffffffe0ff8ffff 0xfbfffffff83fe3ff

def z26 : W := mkw 0xbc436f2bdec3eee9 0x12f10dbcaf7b0fbb 0xfcc7ffffffc7ffff 0xdff31fffffff1fff

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cc647fe0000001e 0x9033191ff8000000

def z28 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xf339b80000000001 0x63cce6e000000000

def z29 : W := mkw 0x0100808000081110 0x0004020200002044 0x030180800078f1f9 0xa80c06020001e3c7

def z30 : W := mkw 0x1059041805d02a42 0x08416410601740a9 0x307804180f800e04 0x40c1e010603e0038

def z31 : W := mkw 0xfbb5b6d420240000 0x03eed6db50809000 0xfffffffff07f003f 0xffffffffffc1fc00

def z32 : W := mkw 0xefee90c16f760000 0x23bfba4305bdd800 0xfffff8e1ffff003f 0xffffffe387fffc00

def z33 : W := mkw 0x1119849001983912 0x08446612400660e4 0x3339808003f8f1f9 0xe8cce602000fe3c7

def z34 : W := mkw 0xefee98c17f7e5114 0x27bfba6305fdf944 0xffffb801ffff702f 0xeffffee007fffdc0

def z35 : W := mkw 0xfff7b6d50c420000 0x03ffdedb54310800 0xffffffff8c47003f 0xf7fffffffe311c00

def z36 : W := mkw 0x1111b6d400000000 0x004446db50000000 0x0001fffe00000010 0x100007fff8000000

def z37 : W := mkw 0xffffb6d56f760000 0x23fffedb55bdd800 0xffffffffffff003f 0xfffffffffffffc00

def z38 : W := mkw 0x0402412388038489 0x001009048e200e12 0x0c86436780070002 0x1432190d9e001c00

def z39 : W := mkw 0x000048209001c088 0x0000012082400702 0xc081f8e1f047f1fb 0x9f0207e387c11fc7

def z40 : W := mkw 0x0100808000000000 0x0004020200000000 0x0301808000000019 0xa00c060200000000

def z41 : W := mkw 0x1111ef989088ff72 0x184447be624223fd 0x0001ff980000ffd0 0x100007fe600003ff

def z42 : W := mkw 0x0000402080018088 0x0000010082000602 0x0cc647ff804781fe 0x9433191ffe011e07

def z43 : W := mkw 0x53999cd031bc7916 0x0d4e667340c6f1e4 0xf339b80073b87001 0x6bcce6e001cee1c0

def z44 : W := mkw 0xfbfdfefcb5fdfbde 0x0feff7fbf2d7f7ef 0xffffffffffffffff 0xffffffffffffffff

def z45 : W := mkw 0xbd7f84994fda3b52 0x2af5fe12653f68ed 0x3f7f84980ff8fffd 0xe8fdfe12603fe3ff

def z46 : W := mkw 0x10012e0010806820 0x104004b8004201a0 0x0001b80000007000 0x000006e0000001c0

def z47 : W := mkw 0x53d9dcf8b5fdfbde 0x0d4f6773e2d7f7ef 0xf3f9fcf9ffffffff 0xffcfe7f3e7ffffff

def z48 : W := mkw 0xfbb5ffd49080ec20 0x13eed7ff524203b0 0xfffffffe0000fe1f 0xf3fffffff80003f8

def z49 : W := mkw 0x0158809805581352 0x080562026015604d 0x037804980c788ffc 0xa00de0126031e23f

def z50 : W := mkw 0x42805860b025c08c 0x050a016182c09702 0xc0807861f0070002 0x170201e187c01c00

def z51 : W := mkw 0x438090c000081110 0x010e024300002044 0xc381f8e00078f1fb 0xbb0e07e38001e3c7

def z52 : W := mkw 0x006e000005520000 0x2001b80000154800 0x007e000000000000 0x0001f80000000000

def z53 : W := mkw 0xbc356f15da80ec20 0x12f0d5bc576a03b0 0xfc7fff1fff80fe37 0xdff1fffc7ffe03f8

def z54 : W := mkw 0x42804800b024c000 0x010a012002c09300 0xc381f801f07ff03b 0xbf0e07e007c1ffc0

def z55 : W := mkw 0xbc7f26154f520000 0x22f1fc98553d4800 0x3c7e071e0f800004 0x40f1f81c783e0000

def z56 : W := mkw 0xac004101ca008400 0x02b0010407280210 0xfc004701ff808e37 0xdff0011c07fe0238

def z57 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xf001b801ff80fe21 0x4fc006e007fe03f8

def z58 : W := mkw 0x0158809805581352 0x080562026015604d 0x03780098007801c8 0x200de0026001e007

def z59 : W := mkw 0x1001040000802800 0x00400410000200a0 0x300184000f80fe35 0xc8c00610003e03f8

def z60 : W := mkw 0x1111849800883b52 0x08444612600220ed 0x000184980000ffd0 0x00000612600003ff

def z61 : W := mkw 0xac006b01da80ec20 0x12b001ac076a03b0 0xcc007b01ff80fe22 0x1f3001ec07fe03f8

def z62 : W := mkw 0xfeef27016ff62c20 0x33fbbc9c05bfd8b0 0xfffe0701ffff0e2f 0xeffff81c07fffc38

def z63 : W := mkw 0x0000402080018088 0x0000010082000602 0x008040e1804781fa 0x9402010386011e07

def z64 : W := mkw 0x47c2d9ebbc6fd7dd 0x051f0b67aef1bf5f 0xcfc7fffffc7fffff 0xbf3f1ffffff1ffff

def z65 : W := mkw 0xeea600016a260000 0x23ba980005a89800 0xcc860001f0070002 0x0732180007c01c00

def z66 : W := mkw 0x0048000805d83b52 0x08012000201760ed 0x000000000ff8ffe0 0x08000000003fe3ff

def z67 : W := mkw 0x0148808005581110 0x0005220200156044 0x337980800ff8f1fd 0xe8cde602003fe3c7

def z68 : W := mkw 0xef80d8e1fa2dd19c 0x07be036387e8b746 0xff81f8e1fffff1ff 0xfffe07e387ffffc7

def z69 : W := mkw 0x4280184030244004 0x050a006100c09100 0xc000380070000000 0x030000e001c00000

def z70 : W := mkw 0xfbbdb6d463340000 0x23eef6db518cd000 0xfffffffe73b8001f 0xfbfffffff9cee000

def z71 : W := mkw 0x1001040000802800 0x00400410000200a0 0x000184000000fe10 0x00000610000003f8

def z72 : W := mkw 0xfaa5364400000000 0x03ea94d910000000 0xfc87ff6600000017 0xd3f21ffd98000000

def z73 : W := mkw 0xb835261400000000 0x02e0d49850000000 0x3c7e071e00000004 0x40f1f81c78000000

def z74 : W := mkw 0xeaa4324400000000 0x03aa90c910000000 0xcc867b6600000002 0x133219ed98000000

def z75 : W := mkw 0x4280000020240000 0x010a000000809000 0xc3800001f07f002b 0xaf0e000007c1fc00

def z76 : W := mkw 0xefeed8e1ff7fd19c 0x27bfbb6387fdff46 0xfffff8e1fffff1ff 0xffffffe387ffffc7

def z77 : W := mkw 0xeba490c000000000 0x03ae924300000000 0xfffff8e00000001f 0xf3ffffe380000000

def z78 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0x038000e1f07ff1e8 0x2c0e000387c1ffc7

def z79 : W := mkw 0xfff7ffffdec3eee9 0x13ffdfffff7b0fbb 0xffffffffffc7ffff 0xffffffffffff1fff

def z80 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfcc7ffffff80fe3f 0xdff31ffffffe03f8

def z81 : W := mkw 0xeea600016a260000 0x23ba980005a89800 0xcf860001f07f002b 0xaf3e180007c1fc00

def z82 : W := mkw 0x000048009000c000 0x0000012002400300 0x0001f8000000f010 0x100007e0000003c0

def z83 : W := mkw 0x1001270000802c20 0x1040049c000200b0 0x0000070000000e00 0x0000001c00000038

def z84 : W := mkw 0x0100d9ea9009d7dd 0x04040367aa40275f 0x0001fffe0000ffd0 0x100007fff80003ff

def z85 : W := mkw 0xb935b6d400000000 0x02e4d6db50000000 0x3c7ffffe00000014 0x50f1fffff8000000

def z86 : W := mkw 0x044a4821ff7fd19c 0x2411292087fdff46 0x00000001fffff1e0 0x0c00000007ffffc7

def z87 : W := mkw 0x0048000005500000 0x0001200000154000 0x337800000ff8002d 0xe8cde000003fe000

def z88 : W := mkw 0x044a00016f760000 0x2011280005bdd800 0x00000001ffff0020 0x0c00000007fffc00

def z89 : W := mkw 0xbc0127014a802c20 0x12f0049c052a00b0 0x3c0007000f800e04 0x40f0001c003e0038

def z90 : W := mkw 0xbc416f09dec0ee60 0x12f105bc277b03b9 0xfc41ff99ffc0ffff 0xdff107fe67ff03ff

def z91 : W := mkw 0x0400410188008400 0x0010010406200210 0x0c00430180000002 0x1430010c06000000

def z92 : W := mkw 0x0400410188008400 0x0010010406200210 0x0c0047018c008e36 0x9430011c06300238

def z93 : W := mkw 0xac6e412bcf5386c9 0x22b1b904af3d4e1b 0x3cfe47ff8fc78ffe 0xd4f3f91ffe3f1e3f

def z94 : W := mkw 0x044200090c420240 0x0011080024310809 0x0cc604998c478ffe 0x8433181266311e3f

def z95 : W := mkw 0x0034001400000000 0x0000d00050000000 0x007e001e00000000 0x0001f80078000000

def z96 : W := mkw 0x10016f009080ec20 0x104005bc024203b0 0x0001ff000000fe10 0x100007fc000003f8

def z97 : W := mkw 0x42ee000025760000 0x210bb8000095d800 0x03fe0000007f0008 0x200ff8000001fc00

def z98 : W := mkw 0x0100808000081110 0x0004020200002044 0x0301800000387001 0x280c06000000e1c0

def z99 : W := mkw 0x0542c1ab8c4b97d9 0x00150b06ae312e5f 0x0fc7c7ff8c7fffff 0xbc3f1f1ffe31ffff

def z100 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc081f8e1f007f1d2 0x170207e387c01fc7

def z101 : W := mkw 0xffff84996ffe3b52 0x2bfffe1265bff8ed 0xffff8499ffffffff 0xeffffe1267ffffff

def z102 : W := mkw 0x000048009000c000 0x0000012002400300 0xc001f801f000f033 0x9f0007e007c003c0

def z103 : W := mkw 0xffefffe1fffffdbc 0x37ffbfff87fffff6 0xffffffe1ffffffff 0xffffffff87ffffff

def z104 : W := mkw 0x04004901da80ec20 0x10100124076a03b0 0x00000001ff80fe20 0x0c00000007fe03f8

def z105 : W := mkw 0x438090e0202d119c 0x050e02438080b446 0x038000e0007f01c8 0x200e00038001fc07

def z106 : W := mkw 0xeaa4000020240000 0x03aa900000809000 0xfffe0001f07f002f 0xeffff80007c1fc00

def z107 : W := mkw 0x47cad8e1ff7fd19c 0x251f2b6387fdff46 0xc381f8e1fffff1fb 0xbf0e07e387ffffc7

def z108 : W := mkw 0xb8012e0052806820 0x12e004b8014a01a0 0xf001bc007f80fe35 0xcbc006f001fe03f8

def z109 : W := mkw 0x1159c4b885d9bbda 0x08456712e21766ef 0x33f9c4f98fffffff 0xfccfe713e63fffff

def z110 : W := mkw 0x0000400080008000 0x0000010002000200 0x0000400180008032 0x9400010006000200

def z111 : W := mkw 0x1111f7fe800186c9 0x004447dffa00061b 0x0001fffe00008fd0 0x100007fff800023f

def z112 : W := mkw 0x0048000805d83b52 0x08012000201760ed 0x337800000ff8ffed 0xe8cde000003fe3ff

def z113 : W := mkw 0xffff84916ffe3912 0x2bfffe1245bff8e4 0xffff8001ffff702f 0xeffffe0007fffdc0

def z114 : W := mkw 0xeaac000063340000 0x23aab000018cd000 0xf338000073b80001 0x6bcce00001cee000

def z115 : W := mkw 0xbc036f23da83eca9 0x12f00dbc8f6a0fb2 0xfc87ff67ff87fe37 0xdff21ffd9ffe1ff8

def z116 : W := mkw 0x0402412b880386c9 0x00100904ae200e1b 0x0c8647ff80078fd2 0x1432191ffe001e3f

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x000047fe00000010 0x1000011ff8000000

def z118 : W := mkw 0xeeee010b6f760641 0x23bbb8042dbdd819 0xfffe071fffff0e2f 0xeffff81c7ffffc38

def z119 : W := mkw 0xff81ffe1faadfdbc 0x17fe07ff87eab7f6 0xff81ffe1ffffffff 0xfffe07ff87ffffff

def z120 : W := mkw 0x044a412b8d5386c9 0x00112904ae354e1b 0x3ffe47ff8fff8fff 0xfcfff91ffe3ffe3f

def z121 : W := mkw 0x4380d8e0b025c08c 0x050e036382c09702 0xc381f8e1f007001b 0xb70e07e387c01c00

def z122 : W := mkw 0x044200010c420000 0x0011080004310800 0x0c4600000c000004 0x0031180000300000

def z123 : W := mkw 0xbc43270b4ec22e61 0x12f10c9c2d3b08b9 0x3c46071e0f800e04 0x40f1181c783e0038

def z124 : W := mkw 0xbc012e015a806820 0x12f004b8056a01a0 0xfc01b801ff807027 0xcff006e007fe01c0

def z125 : W := mkw 0x0442492b9c43c6c9 0x00110924ae710f1b 0xccc7fffffc47ffff 0x9f331ffffff11fff

def z126 : W := mkw 0xfe816f01faa4ec20 0x13fa05bc07ea93b0 0xff81ff01fffffe3f 0xfffe07fc07fffff8

def z127 : W := mkw 0x0542d9eb9c4bd7dd 0x04150b67ae712f5f 0x0cc7ffff8c47fffe 0x94331ffffe311fff

def z128 : W := mkw 0xfeef6f01fff6ec20 0x33fbbdbc07ffdbb0 0xffffff01fffffe3f 0xfffffffc07fffff8

def z129 : W := mkw 0x1111b6d400000000 0x004446db50000000 0x0cc7fffe0000001e 0x90331ffff8000000

def z130 : W := mkw 0x04004901da80ec20 0x10100124076a03b0 0xc001f801ff80fe33 0x9f0007e007fe03f8

def z131 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xf379bc980000001d 0xe3cde6f260000000

def z132 : W := mkw 0xfbb5b6d400802800 0x03eed6db500200a0 0xfffffffe0f80fe3f 0xfbfffffff83e03f8

def z133 : W := mkw 0x044200010c420000 0x0011080004310800 0x000000018c470020 0x0400000006311c00

def z134 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x333980000ff8ffe1 0x68cce600003fe3ff

def z135 : W := mkw 0xeee6412bee6786c9 0x23bb9904afb99e1b 0xccc647fffc478ffe 0x9733191ffff11e3f

def z136 : W := mkw 0x0100d8e09009d19c 0x0404036382402746 0x0001f8e00000f1d0 0x100007e3800003c7

def z137 : W := mkw 0xffc3ffebfeeffffd 0x17ff0fffaffbbfff 0xffc7ffffffffffff 0xffff1fffffffffff

def z138 : W := mkw 0x0400000108000000 0x0010000004200000 0x0c0000018c000026 0x8430000006300000

def z139 : W := mkw 0xfb81fee0f2adf9bc 0x17ee07fb83cab7e6 0xf381f8e1f3fff1fb 0xffce07e387cfffc7

def z140 : W := mkw 0x0000000800883b52 0x08000000200220ed 0x000000000000ffc0 0x00000000000003ff

def z141 : W := mkw 0x1101848000883910 0x00440612000220e4 0x330184800ff8fffd 0xe8cc0612003fe3ff

def z142 : W := mkw 0xffb5fff5faadfdbc 0x17fed7ffd7eab7f6 0xffffffffffffffff 0xffffffffffffffff

def z143 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x037984980078ffd8 0x200de6126001e3ff

def z144 : W := mkw 0xb835261400000000 0x02e0d49850000000 0x3038000000000000 0x40c0e00000000000

def z145 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0c4647fe0c008fd4 0x1031191ff830023f

def z146 : W := mkw 0xbd59ef99dfd8ff72 0x1af567be677f63fd 0xff79ff99fff8ffff 0xfffde7fe67ffe3ff

def z147 : W := mkw 0x438098c0302c5114 0x050e026300c0b144 0xc301b80070387001 0x2b0c06e001c0e1c0

def z148 : W := mkw 0x43b490d400000000 0x010ed24350000000 0x03fe00fe00000008 0x200ff803f8000000

def z149 : W := mkw 0xfbb5fed49000c000 0x03eed7fb52400300 0xfffffffff000f03f 0xffffffffffc003c0

def z150 : W := mkw 0x1553c5bb8c4386c9 0x00554f16ee310e1b 0x3fffc7ff8c478fff 0xf4ffff1ffe311e3f

def z151 : W := mkw 0x0400010108000400 0x0010000404200010 0x0c0007000c000e04 0x0030001c00300038

def z152 : W := mkw 0x1059041805d02a42 0x08416410601740a9 0x307804980fc08ffc 0xc0c1e012603f023f

def z153 : W := mkw 0x155b84990dda3b52 0x08556e12643768ed 0x3fff84998fffffff 0xecfffe12663fffff

def z154 : W := mkw 0xfbfdb6d405500000 0x03eff6db50154000 0xfffffffe0ff8003f 0xfbfffffff83fe000

def z155 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xcc87fffe00000012 0x13321ffff8000000

def z156 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0x3ffe07fe0000000c 0x60fff81ff8000000

def z157 : W := mkw 0x0400412b880186c9 0x00100104ae20061b 0x0c0047ff8c008ff6 0x9430011ffe30023f

def z158 : W := mkw 0x46ee00012d760000 0x211bb80004b5d800 0x0ffe00018c7f002e 0xa43ff8000631fc00

def z159 : W := mkw 0x000049009080ec20 0x10000124024203b0 0x000000000000fe00 0x00000000000003f8

def z160 : W := mkw 0x000048009000c000 0x0000012002400300 0xc0007801f0000002 0x170001e007c00000

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c00470000000016 0x9030011c00000000

def z162 : W := mkw 0xa800000042000000 0x02a0000001080000 0xf000000073800001 0x4bc0000001ce0000

def z163 : W := mkw 0xfbfdb6dc05581352 0x0beff6db7015604d 0xfffffffe007801df 0xf3fffffff801e007

def z164 : W := mkw 0xeaa47a64b025c08c 0x07aa91e992c09702 0xcc867b67f0070002 0x173219ed9fc01c00

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0x000004000c008e34 0x8000001000300238

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c86436600000002 0x1032190d98000000

def z167 : W := mkw 0x10016f2a9081eee9 0x104005bcaa4207bb 0x0001fffe0000ffd0 0x100007fff80003ff

def z168 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xcfc7fffff07ff1ff 0xbf3f1fffffc1ffc7

def z169 : W := mkw 0xfbfdb6dc05d02a42 0x0beff6db701740a9 0xfffffffe0f800e1f 0xf3fffffff83e0038

def z170 : W := mkw 0x4280104000000000 0x010a004100000000 0xc080786000000002 0x130201e180000000

def z171 : W := mkw 0xfbbdb6d401983912 0x0beef6db500660e4 0xf339b80003b87001 0x6bcce6e0000ee1c0

def z172 : W := mkw 0x04004921faadfdbc 0x1410012487eab7f6 0x00000001ffffffe0 0x0c00000007ffffff

def z173 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0x3c01ff000f80fe14 0x50f007fc003e03f8

def z174 : W := mkw 0x4380d8c09000c000 0x010e036302400300 0xc381f8e1f000f03b 0xbf0e07e387c003c0

def z175 : W := mkw 0xffffc5bbefffbfdb 0x2bffff16efbffeff 0xffffc7ffffffffff 0xffffff1fffffffff

def z176 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x000000018c478fe0 0x0400000006311e3f

def z177 : W := mkw 0xb801260000000000 0x02e0049800000000 0x3c00070000000004 0x40f0001c00000000

def z178 : W := mkw 0x438090c000000000 0x010e024300000000 0xc381f8e00000001b 0xb30e07e380000000

def z179 : W := mkw 0x5399dcf0b1bdf99e 0x0d4e6773c2c6f7e6 0xf3b9f8e1f3fff1fb 0xffcee7e387cfffc7

def z180 : W := mkw 0xeaa4000000000000 0x03aa900000000000 0xfffe00000000000f 0xe3fff80000000000

def z181 : W := mkw 0x0000402080018088 0x0000010082000602 0x0080406180070002 0x1402010186001c00

def z182 : W := mkw 0x1119849001983912 0x08446612400660e4 0x3339800003b87001 0x68cce600000ee1c0

def z183 : W := mkw 0x115b84ba05db3bdb 0x08456e12e8176cef 0x33ff84fe0ffffffd 0xe8cffe13f83fffff

def z184 : W := mkw 0xac006b01da00c420 0x12b001ac07680310 0xcc01fb01f000f033 0x9f3007ec07c003c0

def z185 : W := mkw 0x47f6d1ff8c4386c9 0x011fdb47fe310e1b 0x0ffe47ff8c478ffe 0xb43ff91ffe311e3f

def z186 : W := mkw 0x0048000805d02a42 0x08012000201740a9 0x000000000f800e00 0x00000000003e0038

def z187 : W := mkw 0xffffb6dd6ffe3b52 0x2bfffedb75bff8ed 0xffffffffffffffff 0xffffffffffffffff

def z188 : W := mkw 0xa824000000000000 0x02a0900000000000 0x3c7e000000000004 0x40f1f80000000000

def z189 : W := mkw 0xeeee4821ff7fd19c 0x27bbb92087fdff46 0xfffe0001fffff1ef 0xeffff80007ffffc7

def z190 : W := mkw 0xbc43672b8c4386c9 0x02f10d9cae310e1b 0xfcc7ffff8c478fff 0xd7f31ffffe311e3f

def z191 : W := mkw 0x1111dcf89089fbde 0x0c444773e24227ef 0x0001fcf80000ffd0 0x100007f3e00003ff

def z192 : W := mkw 0x0158809805d83b52 0x08056202601760ed 0x037800980ff8ffe8 0x280de002603fe3ff

def z193 : W := mkw 0x1111b6d400000000 0x004446db50000000 0x0001b80000000000 0x000006e000000000

def z194 : W := mkw 0xfbfd849867fc3b52 0x2beff612619ff0ed 0xf37984987ff8fffd 0xebcde61261ffe3ff

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300000000780029 0xa80c00000001e000

def z196 : W := mkw 0xfbb5bed4302c5114 0x07eed6fb50c0b144 0xf339b80070387001 0x6bcce6e001c0e1c0

def z197 : W := mkw 0xfeef04016ff62800 0x23fbbc1005bfd8a0 0xffff8401fffffe3f 0xeffffe1007fffff8

def z198 : W := mkw 0x044241238c438489 0x001109048e310e12 0x0cc643678c47002e 0x9433190d9e311c00

def z199 : W := mkw 0xbd5befbbdfdbfffb 0x1af56fbeef7f6fff 0xffffffffffffffff 0xffffffffffffffff

def z200 : W := mkw 0x0008000001983912 0x08002000000660e4 0x0000000003b87000 0x08000000000ee1c0

def z201 : W := mkw 0x0400412188018488 0x0010010486200612 0x0c8047e18c478ffe 0x9432011f86311e3f

def z202 : W := mkw 0x4380d0e0a02d919c 0x050e03438280b646 0x038040e1807f81fa 0xb40e01038601fe07

def z203 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0x3ffe00000fff000c 0x60fff800003ffc00

def z204 : W := mkw 0x0000000020240000 0x0000000000809000 0x00000001f07f0020 0x0c00000007c1fc00

def z205 : W := mkw 0x46ee00016f760000 0x211bb80005bdd800 0x03fe0001ffff0028 0x2c0ff80007fffc00

def z206 : W := mkw 0x438090e0202d119c 0x050e02438080b446 0xc381f8e0007f01db 0xb30e07e38001fc07

def z207 : W := mkw 0x1049040805d83b52 0x08412410201760ed 0x300184000ff8fff5 0xc8c00610003fe3ff

def z208 : W := mkw 0x4780d9e1b82dd59c 0x051e036786e0b756 0xcf81ffe1fc7fffff 0xbf3e07ff87f1ffff

def z209 : W := mkw 0x0442010b0c420641 0x001108042c310819 0x0cc647fe0c000e1e 0x9033191ff8300038

def z210 : W := mkw 0x1159849805d02a42 0x08456612601740a9 0x337984980f800e1d 0xe0cde612603e0038

def z211 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0c0047018c478ff6 0x9430011c06311e3f

def z212 : W := mkw 0xfff7f7ff8c4386c9 0x03ffdfdffe310e1b 0xffffffff8c478fff 0xf7fffffffe311e3f

def z213 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0c8643678c478fe2 0x1432190d9e311e3f

def z214 : W := mkw 0x5381ffe0b0adfdbc 0x154e07ff82c2b7f6 0xc381ffe1f07ffffb 0xbf0e07ff87c1ffff

def z215 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x000184980ff8fff0 0x08000612603fe3ff

def z216 : W := mkw 0xeee600016e660000 0x23bb980005b99800 0xccc60001fc47002e 0x8733180007f11c00

def z217 : W := mkw 0x0042002a044302c9 0x00010800a8110c0b 0x00c600fe004701c8 0x00031803f8011c07

def z218 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe47ffffff003f 0xfffff91ffffffc00

def z219 : W := mkw 0x1111849800883b52 0x08444612600220ed 0x300184980f80fff5 0xc8c00612603e03ff

def z220 : W := mkw 0x438090c000000000 0x010e024300000000 0xcfc7fffe0000001f 0xb33f1ffff8000000

def z221 : W := mkw 0x0000002a000102c9 0x00000000a800040b 0x000000fe000001c0 0x00000003f8000007

def z222 : W := mkw 0xfbb5f7fe800186c9 0x03eed7dffa00061b 0xfffffffe00008fdf 0xf3fffffff800023f

def z223 : W := mkw 0x0000412a800186c9 0x00000104aa00061b 0x000047fe00008fd0 0x1000011ff800023f

def z224 : W := mkw 0x0000000000081110 0x0000000000002044 0x000000000078f1e0 0x080000000001e3c7

def z225 : W := mkw 0xfea57f45da80ec20 0x13fa95fd176a03b0 0xfc87ff67ff80fe37 0xdff21ffd9ffe03f8

def z226 : W := mkw 0x044a412bef7786c9 0x20112904afbdde1b 0x0cc647ffffff8ffe 0x9c33191ffffffe3f

def z227 : W := mkw 0x0442410b8c428641 0x001109042e310a19 0x0c46471f8c008e36 0x9431191c7e300238

def z228 : W := mkw 0xfbbdb6d401983912 0x0beef6db500660e4 0xfffffffe03b8701f 0xfbfffffff80ee1c0

def z229 : W := mkw 0x1159b6dc05d83b52 0x084566db701760ed 0x3379fffe0ff8fffd 0xf8cde7fff83fe3ff

def z230 : W := mkw 0xac004901da80ec20 0x12b00124076a03b0 0xfc000001ff80fe27 0xcff0000007fe03f8

def z231 : W := mkw 0xfbb5fef4b02dd19c 0x07eed7fbd2c0b746 0xf3b9f8e1f07ff1fb 0xffcee7e387c1ffc7

def z232 : W := mkw 0x1011041800802a42 0x08404410600200a9 0x0000041800000e00 0x0000001060000038

def z233 : W := mkw 0x044a00016f760000 0x2011280005bdd800 0x33780001ffff002d 0xeccde00007fffc00

def z234 : W := mkw 0x0000412a800186c9 0x00000104aa00061b 0x0000000000008fc0 0x000000000000023f

def z235 : W := mkw 0x53fd94dc05d83b52 0x094ff653701760ed 0x33ff84fe0ff8fffd 0xe8cffe13f83fe3ff

def z236 : W := mkw 0xac0000014a000000 0x02b0000005280000 0xfc000001ff800027 0xcff0000007fe0000

def z237 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xf3380001ffff0021 0x6fcce00007fffc00

def z238 : W := mkw 0x00004820b02dd19c 0x0400012082c0b746 0x008040e1f07ff1fa 0x9c02010387c1ffc7

def z239 : W := mkw 0x1101ffe09089fdbc 0x144407ff824227f6 0x0001ffe00000ffd0 0x100007ff800003ff

def z240 : W := mkw 0xffb5b7d54a802c20 0x13fed6df552a00b0 0xfffffffe0f800e1f 0xf3fffffff83e0038

def z241 : W := mkw 0xeeee4123ef778489 0x23bbb9048fbdde12 0xfffe4367ffff002f 0xfffff90d9ffffc00

def z242 : W := mkw 0xbc012f015a806c20 0x12f004bc056a01b0 0xfc01bf007f807e05 0x4bf006fc01fe01f8

def z243 : W := mkw 0x0058001805500242 0x0801600060154009 0x0078001800000000 0x0001e00060000000

def z244 : W := mkw 0x0118809001181112 0x0804620240046044 0x0338000000380000 0x200ce0000000e000

def z245 : W := mkw 0xbc016f2bda81eee9 0x12f005bcaf6a07bb 0xfc01ffffff80fff7 0xdff007fffffe03ff

def z246 : W := mkw 0xac006b01da00c420 0x12b001ac07680310 0xcc007b01f0000002 0x173001ec07c00000

def z247 : W := mkw 0x46c2412bac6786c9 0x011b0904aeb19e1b 0xcfc647fffc7f8fff 0xbf3f191ffff1fe3f

def z248 : W := mkw 0xeea66b01fa26c420 0x33ba99ac07e89b10 0xcc867b01f0070002 0x173219ec07c01c00

def z249 : W := mkw 0x010098c010085114 0x0404026300402144 0x0001b80000007000 0x000006e0000001c0

def z250 : W := mkw 0xfbb5bed4302c5114 0x07eed6fb50c0b144 0xfffffffe7038701f 0xfbfffffff9c0e1c0

def z251 : W := mkw 0xb8012e0052806820 0x12e004b8014a01a0 0xf001b80073807001 0x4bc006e001ce01c0

def z252 : W := mkw 0x4280000020240000 0x010a000000809000 0xc300000070380001 0x2b0c000001c0e000

def z253 : W := mkw 0x044a412b8ddbbfdb 0x08112904ae376eff 0x0cc647ff8ffffffe 0x9c33191ffe3fffff

def z254 : W := mkw 0xfaa5260000000000 0x03ea949800000000 0xffffff000000001f 0xf3fffffc00000000

def z255 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfcfe0001ff870006 0x47f3f80007fe1c00

def z256 : W := mkw 0xac426b2bde43c6e9 0x12b109acaf790f1b 0xccc67ffffc478ffe 0x973319fffff11e3f

def z257 : W := mkw 0x00004820b025c08c 0x0400012082c09702 0x00000001f0070000 0x0400000007c01c00

def z258 : W := mkw 0xeee6736f8c4386c9 0x03bb99cdbe310e1b 0xccc67fff8c478ffe 0x973319fffe311e3f

def z259 : W := mkw 0x1559cd99dfd8ff72 0x18556736677f63fd 0x33798499fff8fffd 0xeccde61267ffe3ff

def z260 : W := mkw 0x1159849005d83912 0x08456612401760e4 0x337980000ff8702d 0xe8cde600003fe1c0

def z261 : W := mkw 0xebb4b2d400000000 0x03aed2cb50000000 0xcffe7bfe0000000a 0x333ff9eff8000000

def z262 : W := mkw 0x0008000063340000 0x20002000018cd000 0x0000000073b80000 0x0800000001cee000

def z263 : W := mkw 0xbc77673f8c4386c9 0x02f1dd9cfe310e1b 0x3cfe47ff8c478ffe 0xd4f3f91ffe311e3f

def z264 : W := mkw 0x43fe90d425760000 0x210ffa435095d800 0x03fe00fe007f0008 0x200ff803f801fc00

def z265 : W := mkw 0x0042002a044302c9 0x00010800a8110c0b 0x00000000004701c0 0x0000000000011c07

def z266 : W := mkw 0x43ee90e0257f119c 0x250fba438095fc46 0x03fe00e0007f01c8 0x200ff8038001fc07

def z267 : W := mkw 0xfaad2e0073b46820 0x33eab4b801ced1a0 0xf339b80073b87001 0x6bcce6e001cee1c0

def z268 : W := mkw 0x438090e0202d119c 0x050e02438080b446 0xc38000e1f07f01eb 0xaf0e000387c1fc07

def z269 : W := mkw 0x0402000108020000 0x0010080004200800 0x0c86000180070002 0x0432180006001c00

def z270 : W := mkw 0xfbb5f6f480018088 0x03eed7dbd2000602 0xffffffff804781ff 0xf7fffffffe011e07

def z271 : W := mkw 0x0048000805500240 0x0001200020154009 0x337804980ff88ffd 0xe8cde012603fe23f

def z272 : W := mkw 0x43f690fe044302c9 0x010fda43f8110c0b 0x03fe00fe004701c8 0x200ff803f8011c07

def z273 : W := mkw 0xeffe90d56f760000 0x23bffa4355bdd800 0xfffe00ffffff002f 0xeffff803fffffc00

def z274 : W := mkw 0x0402412388038489 0x001009048e200e12 0x0cc647ff8007001e 0x9433191ffe001c00

def z275 : W := mkw 0x4782d9e3b82fd59d 0x051e0b678ee0bf56 0xcf87fbe7f07ff1fb 0xbf3e1fef9fc1ffc7

def z276 : W := mkw 0x1111849000000000 0x0044461240000000 0x3339800000000001 0x60cce60000000000

def z277 : W := mkw 0x0442010b0c420641 0x001108042c310819 0x0c46071e0c000e04 0x0031181c78300038

def z278 : W := mkw 0xefee90e16f7f119c 0x27bfba4385bdfc46 0xfffe00e1ffff01ef 0xeffff80387fffc07

def z279 : W := mkw 0x011090d400000000 0x0004424350000000 0x000000fe00000000 0x00000003f8000000

def z280 : W := mkw 0x0100808000081110 0x0004020200002044 0x000180800000f1d0 0x00000602000003c7

def z281 : W := mkw 0xeba4b2c400000000 0x03ae92cb10000000 0xcf87fbe60000001b 0xb33e1fef98000000

def z282 : W := mkw 0x000048209009d19c 0x0400012082402746 0x000000000000f1c0 0x00000000000003c7

def z283 : W := mkw 0xffffffd5fff6ec20 0x33ffffff57ffdbb0 0xfffffffffffffe3f 0xfffffffffffffff8

def z284 : W := mkw 0x044a412bef7786c9 0x20112904afbdde1b 0x00000001ffff8fe0 0x0c00000007fffe3f

def z285 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc301b801f07ff1e1 0x2f0c06e007c1ffc7

def z286 : W := mkw 0x0000000000802800 0x00000000000200a0 0x000000000f80fe20 0x08000000003e03f8

def z287 : W := mkw 0x53b5b6d400000000 0x014ed6db50000000 0x03fffffe00000018 0x300ffffff8000000

def z288 : W := mkw 0x0100d8e09009d19c 0x0404036382402746 0x0081f8e18047f1fa 0x940207e386011fc7

def z289 : W := mkw 0xfeff04196ff62a42 0x2bfbfc1065bfd8a9 0xfffe0419ffff0e2f 0xeffff81067fffc38

def z290 : W := mkw 0x1159cc9895d8fb52 0x08456732625763ed 0xf379fc99fff8ffff 0xffcde7f267ffe3ff

def z291 : W := mkw 0xfb81fee0b02dd19c 0x07ee07fb82c0b746 0xff81ffe1f07ff1ff 0xfffe07ff87c1ffc7

def z292 : W := mkw 0x0042000a04420241 0x0001080028110809 0x0046001e00000000 0x0001180078000000

def z293 : W := mkw 0x4380d0e080018088 0x010e034382000602 0xc381f8e1804781fb 0xb70e07e386011e07

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000000f800025 0xc8c00000003e0000

def z295 : W := mkw 0x1049040005d02800 0x00412410001740a0 0x337984000ff8fe3d 0xe8cde610003fe3f8

def z296 : W := mkw 0xeaa4000000000000 0x03aa900000000000 0xcc86000000000002 0x0332180000000000

def z297 : W := mkw 0xee8000016a240000 0x03ba000005a89000 0xff800001ffff002f 0xeffe000007fffc00

def z298 : W := mkw 0x1011041000000000 0x0040441040000000 0x3078041800000004 0x40c1e01060000000

def z299 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc38078e1f07f01ca 0x370e01e387c1fc07

def z300 : W := mkw 0xbd11ef91da80ec20 0x12f447be476a03b0 0xff79ff99ff80fe3f 0xfffde7fe67fe03f8

def z301 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc6477f8c070e06 0x1433191dfe301c38

def z302 : W := mkw 0x438090c000000000 0x010e024300000000 0x038000e000000008 0x200e000380000000

def z303 : W := mkw 0xac6e00014f520000 0x22b1b800053d4800 0x3c7e00000f800004 0x40f1f800003e0000

def z304 : W := mkw 0xfbb5fef49009d19c 0x07eed7fbd2402746 0xfffffffe0000f1df 0xf3fffffff80003c7

def z305 : W := mkw 0x044a00016f760000 0x2011280005bdd800 0x0cc60001ffff002e 0x8c33180007fffc00

def z306 : W := mkw 0x42c8000025740000 0x010b20000095d000 0xf3f80001ffff002f 0xefcfe00007fffc00

def z307 : W := mkw 0x0100c8809008d110 0x0004032202402344 0xc301f881f078f1fb 0xbf0c07e207c1e3c7

def z308 : W := mkw 0x0048000805581352 0x080120002015604d 0x00000000007801c0 0x000000000001e007

def z309 : W := mkw 0x0442012b0c4306c9 0x00110804ac310c1b 0x0cc607fe0c470fcc 0x0033181ff8311c3f

def z310 : W := mkw 0x1111849000802800 0x00444612400200a0 0x337984980f80fe3d 0xe8cde612603e03f8

def z311 : W := mkw 0x00004820b02dd19c 0x0400012082c0b746 0xc001f801f07ff1f3 0x9f0007e007c1ffc7

def z312 : W := mkw 0xeaec000067740000 0x23abb000019dd000 0xf37800007ff8002d 0xebcde00001ffe000

def z313 : W := mkw 0xbc016701ca80ac20 0x12f0059c072a02b0 0x3c0047018f808e36 0xd4f0011c063e0238

def z314 : W := mkw 0x4380d8c0b02cd114 0x050e036302c0b344 0xc301f801f038f033 0xbf0c07e007c0e3c0

def z315 : W := mkw 0x044a412b8ddbbfdb 0x08112904ae376eff 0x000000018fffffe0 0x0c000000063fffff

def z316 : W := mkw 0x53d99cd835fc7b56 0x0d4f667360d7f1ed 0xf379bc987ff8fffd 0xebcde6f261ffe3ff

def z317 : W := mkw 0xfbb5b6d400081110 0x03eed6db50002044 0xfffffffe0078f1ff 0xfbfffffff801e3c7

def z318 : W := mkw 0xbc6f27014fd22c20 0x32f1bc9c053f48b0 0x3c7e07000f800e04 0x40f1f81c003e0038

def z319 : W := mkw 0xffffdcf9fffffbde 0x2fffff73e7ffffef 0xfffffcf9ffffffff 0xfffffff3e7ffffff

def z320 : W := mkw 0x4280000000000000 0x010a000000000000 0xc38000000000000b 0xa30e000000000000

def z321 : W := mkw 0xfbf7b6fe044302c9 0x03efdedbf8110c0b 0xfffffffe004701df 0xf3fffffff8011c07

def z322 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x004004998c478ffc 0x8401001266311e3f

def z323 : W := mkw 0x0100c0a080099198 0x0004030282002646 0x0381c0e1807ff1fb 0xbc0e07038601ffc7

def z324 : W := mkw 0xb8012e0052806820 0x12e004b8014a01a0 0xfc01ff0073807017 0xdbf007fc01ce01c0

def z325 : W := mkw 0x10014c009080e800 0x00400530024203a0 0xf001fc01ff80fe37 0xdfc007f007fe03f8

def z326 : W := mkw 0xbd11ef99da88ff72 0x1af447be676a23fd 0xfc01ff99ff80fff7 0xdff007fe67fe03ff

def z327 : W := mkw 0xffb5b6d54a000000 0x03fed6db55280000 0xffffffffff80003f 0xfffffffffffe0000

def z328 : W := mkw 0x1001260000000000 0x0040049800000000 0x0001ff0000000010 0x100007fc00000000

def z329 : W := mkw 0x140145018880ac00 0x00500514062202b0 0x3c01c7018f80fe37 0xdcf0071c063e03f8

def z330 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xff7fbf1e00000005 0x63fdfefc78000000

def z331 : W := mkw 0x0000010a00000641 0x0000000428000019 0x0000071e00000e00 0x0000001c78000038

def z332 : W := mkw 0x47c2d9ebbc6fd7dd 0x051f0b67aef1bf5f 0xc381f8e1fc7ffffb 0xbf0e07e387f1ffff

def z333 : W := mkw 0x0148808805d83b52 0x08052202201760ed 0x030180800ff8fff9 0xa80c0602003fe3ff

def z334 : W := mkw 0x42ee002a257702c9 0x210bb800a895dc0b 0x03fe00fe007f01c8 0x200ff803f801fc07

def z335 : W := mkw 0xfe817f61faa5ecac 0x17fa05fd87ea97b2 0xfc81ff61ff87fe37 0xdff207fd87fe1ff8

def z336 : W := mkw 0xac006b01da00c420 0x12b001ac07680310 0xfc007b01ff800027 0xdff001ec07fe0000

def z337 : W := mkw 0xbc016f21da81eca8 0x12f005bc876a07b2 0xfc81ffe1ffc7ffff 0xdff207ff87ff1fff

def z338 : W := mkw 0x438098c0302c5114 0x050e026300c0b144 0xc381b801f07f702b 0xaf0e06e007c1fdc0

def z339 : W := mkw 0xef80fbe1fa2dd5bc 0x17be03ef87e8b756 0xcf81fbe1f07ff1fb 0xbf3e07ef87c1ffc7

def z340 : W := mkw 0x155bc5bb8ddbbfdb 0x08556f16ee376eff 0x337984998ffffffd 0xeccde612663fffff

def z341 : W := mkw 0xeea632456a260000 0x23ba98c915a89800 0xcc867b67f0070002 0x173219ed9fc01c00

def z342 : W := mkw 0xfbfd849805d83b52 0x0beff612601760ed 0xffff84980ff8ffff 0xebfffe12603fe3ff

def z343 : W := mkw 0xbc596f19dfd0ee62 0x1af165bc677f43b9 0xfc79ff19ff80fe37 0xdff1e7fc67fe03f8

def z344 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x3fffc7fe0ff8ffff 0xf8ffff1ff83fe3ff

def z345 : W := mkw 0xeeee00096ffe3b52 0x2bbbb80025bff8ed 0xfffe0001ffffffef 0xeffff80007ffffff

def z346 : W := mkw 0xee807b61fa25c4ac 0x17ba01ed87e89712 0xcc807b61f0070002 0x173201ed87c01c00

def z347 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xcc01ff01f000fe12 0x173007fc07c003f8

def z348 : W := mkw 0x044240218c438088 0x0011090086310e02 0x0cc640e18c4781fe 0x9433190386311e07

def z349 : W := mkw 0x0000324400000000 0x000000c910000000 0x00007b6600000000 0x100001ed98000000

def z350 : W := mkw 0xffff84916f760000 0x23fffe1245bdd800 0xffff8499ffff003f 0xeffffe1267fffc00

def z351 : W := mkw 0x1159849805581352 0x084566126015604d 0x33798498007801dd 0xe0cde6126001e007

def z352 : W := mkw 0x04004901da80ec20 0x10100124076a03b0 0x0c004701ff80fe36 0x9c30011c07fe03f8

def z353 : W := mkw 0x5391dcf8b0adfbde 0x0d4e4773e2c2b7ef 0xc381fcf9f07ffffb 0xbf0e07f3e7c1ffff

def z354 : W := mkw 0x0042412a844386c9 0x00010904aa110e1b 0x00c647fe00478fd8 0x1003191ff8011e3f

def z355 : W := mkw 0x43c8d8e8b5fdfbde 0x0d0f2363a2d7f7ef 0xc381f8e1fffffffb 0xbf0e07e387ffffff

def z356 : W := mkw 0x14436f2b9cc3eee9 0x10510dbcae730fbb 0x0cc7ffff8c47fffe 0x94331ffffe311fff

def z357 : W := mkw 0xefee80816f7e1110 0x23bfba0205bdf844 0xffff8081fffff1ff 0xeffffe0207ffffc7

def z358 : W := mkw 0xbc7f04194fd22a42 0x2af1fc10653f48a9 0x3c7e04180f800e04 0x40f1f810603e0038

def z359 : W := mkw 0xeaac000063340000 0x23aab000018cd000 0xf3b80001f3ff002b 0xefcee00007cffc00

def z360 : W := mkw 0x1041040804c02a40 0x00410410201300a9 0x304184980fc0fffd 0xc8c10612603f03ff

def z361 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xff39ff0000000017 0xf3fce7fc00000000

def z362 : W := mkw 0xbc4b6f01fff6ec20 0x32f12dbc07ffdbb0 0xfc01ff01fffffe37 0xdff007fc07fffff8

def z363 : W := mkw 0xeeee4021ef778088 0x23bbb90087bdde02 0xfffe40e1ffff81ff 0xfffff90387fffe07

def z364 : W := mkw 0xeeee00014f520000 0x23bbb800053d4800 0xfffe00000f80000f 0xe3fff800003e0000

def z365 : W := mkw 0x4380d9eab02dd7dd 0x050e0367aac0b75f 0xc381fffff07ffffb 0xbf0e07ffffc1ffff

def z366 : W := mkw 0x0000412a800186c9 0x00000104aa00061b 0x008047ff80478ffa 0x9402011ffe011e3f

def z367 : W := mkw 0xb911b6d400000000 0x02e446db50000000 0xfc01fffe00000017 0xd3f007fff8000000

def z368 : W := mkw 0xfbb5bed452806820 0x13eed6fb514a01a0 0xf339b80073807001 0x6bcce6e001ce01c0

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000080004081f8 0x8000000200010207

def z370 : W := mkw 0xffffb6d56f760000 0x23fffedb55bdd800 0xffffb801ffff002f 0xeffffee007fffc00

def z371 : W := mkw 0x0000000000000000 0x0000000000000000 0x337800000000000d 0xe0cde00000000000

def z372 : W := mkw 0x044a4901fff6ec20 0x3011292407ffdbb0 0x00000001fffffe20 0x0c00000007fffff8

def z373 : W := mkw 0xb801260000000000 0x02e0049800000000 0xfcc7fffe0000001f 0xd3f31ffff8000000

def z374 : W := mkw 0xfbb5b6f4202d119c 0x07eed6dbd080b446 0xfffffffe007f01df 0xf3fffffff801fc07

def z375 : W := mkw 0x0040000004400000 0x0001000000110000 0x004000000c40002c 0x8001000000310000

def z376 : W := mkw 0xeeae00016b360000 0x23bab80005acd800 0xffbe0001f3bf0003 0x6ffef80007cefc00

def z377 : W := mkw 0xeaa4000000000000 0x03aa900000000000 0xf338000000000001 0x63cce00000000000

def z378 : W := mkw 0xfea76f01faa6ec20 0x33fa9dbc07ea9bb0 0xfc87ff01ff87fe37 0xdff21ffc07fe1ff8

def z379 : W := mkw 0x1059041805d02a42 0x08416410601740a9 0x307984180f80fe35 0xc8c1e610603e03f8

def z380 : W := mkw 0xac6e00014f520000 0x22b1b800053d4800 0xfc7e0001ff800027 0xcff1f80007fe0000

def z381 : W := mkw 0xbc43672bcec3aee9 0x12f10d9caf3b0ebb 0x3cc647ff8fc78ffe 0xd4f3191ffe3f1e3f

def z382 : W := mkw 0x0158809805581352 0x080562026015604d 0x337800980ff801ed 0xe8cde002603fe007

def z383 : W := mkw 0x1111ffd49080ec20 0x104447ff524203b0 0x0001fffe0000fe10 0x100007fff80003f8

def z384 : W := mkw 0xeba4d8e0b02dd19c 0x07ae936382c0b746 0xfffff8e1f07ff1ff 0xffffffe387c1ffc7

def z385 : W := mkw 0x1111849800883b52 0x08444612600220ed 0x030184980078fff9 0xa80c06126001e3ff

def z386 : W := mkw 0xffb7f7f788038489 0x03fedfdfde200e12 0xffffffff8007001f 0xf7fffffffe001c00

def z387 : W := mkw 0xb97da69c05d83b52 0x0ae5f69a701760ed 0x3f7f879e0ff8fffd 0xe8fdfe1e783fe3ff

def z388 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xf3b9f8e00000001b 0xf3cee7e380000000

def z389 : W := mkw 0x42a6000020260000 0x210a980000809800 0x0086000000070000 0x0002180000001c00

def z390 : W := mkw 0x4280000020240000 0x010a000000809000 0x03800000007f0008 0x200e00000001fc00

def z391 : W := mkw 0x0158809805581352 0x080562026015604d 0x037980980078f1f9 0xa80de6026001e3c7

def z392 : W := mkw 0x42a4104400000000 0x010a904110000000 0x0086006600000000 0x0002180198000000

def z393 : W := mkw 0x0442492bbc6fd7dd 0x04110924aef1bf5f 0x00000001fc7fffe0 0x0c00000007f1ffff

def z394 : W := mkw 0x43b490f4202d119c 0x050ed243d080b446 0x03fe00fe007f01c8 0x200ff803f801fc07

def z395 : W := mkw 0x0040000804400240 0x0001000020110009 0x000000000c408fe0 0x000000000031023f

def z396 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc301f8e07038f1d1 0x3b0c07e381c0e3c7

def z397 : W := mkw 0xbc01670188008400 0x02f0059c06200210 0xfc01ff018c008e37 0xd7f007fc06300238

def z398 : W := mkw 0xbd01ef81da88fd30 0x12f407be076a23f4 0xff01ff81fff8ffff 0xfffc07fe07ffe3ff

def z399 : W := mkw 0x0110809800081352 0x080442026000204d 0x00000098000001c0 0x0000000260000007

def z400 : W := mkw 0x0040412a844186c9 0x00010104aa11061b 0x004047fe0c408ffc 0x9001011ff831023f

def z401 : W := mkw 0x10016f009080ec20 0x104005bc024203b0 0x3001ff000f80fe35 0xd8c007fc003e03f8

def z402 : W := mkw 0xeeac00016b340000 0x23bab00005acd000 0xff380001ffb80027 0xeffce00007fee000

def z403 : W := mkw 0x1119849801983b52 0x08446612600660ed 0x3339849803b8ffd1 0x68cce612600ee3ff

def z404 : W := mkw 0x0100c8a0b02dd19c 0x0404032282c0b746 0x03018081f07ff1f9 0xac0c060207c1ffc7

def z405 : W := mkw 0x0400410188008400 0x0010010406200210 0x0cc647ff8c008e3e 0x9433191ffe300238

def z406 : W := mkw 0x1111849000000000 0x0044461240000000 0x3fffc7fe0000001f 0xf0ffff1ff8000000

def z407 : W := mkw 0xb801260042802820 0x12e00498010a00a0 0x3000000003800000 0x40c00000000e0000

def z408 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xf339fffe00000011 0x73cce7fff8000000

def z409 : W := mkw 0x43eed8e0b57fd19c 0x250fbb6382d5ff46 0xc3fff8e1f07ff1fb 0xbf0fffe387c1ffc7

def z410 : W := mkw 0xac6e00014f520000 0x22b1b800053d4800 0x3cfe00018fc7002e 0xc4f3f800063f1c00

def z411 : W := mkw 0xefa6d8e1fa2fd19c 0x27be9b6387e8bf46 0xcf87f8e1f07ff1fb 0xbf3e1fe387c1ffc7

def z412 : W := mkw 0xbc0127014a802c20 0x12f0049c052a00b0 0xfc01ff000f800e17 0xd3f007fc003e0038

def z413 : W := mkw 0x04004901da00c420 0x1010012407680310 0x00000001f0000000 0x0400000007c00000

def z414 : W := mkw 0x1159dcf895d9fbde 0x0c456773e25767ef 0x3379fcf80ff8fffd 0xf8cde7f3e03fe3ff

def z415 : W := mkw 0xbc436f0bdec2ee61 0x12f10dbc2f7b0bb9 0xfc47ff1fff80fe37 0xdff11ffc7ffe03f8

def z416 : W := mkw 0x53d994f825fd3bde 0x0d4f6653e097f4ef 0x33f984f80ffffffd 0xe8cfe613e03fffff

def z417 : W := mkw 0xeaa4000000000000 0x03aa900000000000 0xfffe47fe0000001f 0xf3fff91ff8000000

def z418 : W := mkw 0xbc016f01da00c420 0x12f005bc07680310 0xfc01ff01f0000017 0xd7f007fc07c00000

def z419 : W := mkw 0xeea600016a260000 0x23ba980005a89800 0xfffe0001f007000f 0xe7fff80007c01c00

def z420 : W := mkw 0xb8016f009080ec20 0x12e005bc024203b0 0xfc01ff000000fe17 0xd3f007fc000003f8

def z421 : W := mkw 0x43fc90dc05581352 0x090ff2437015604d 0x03fe00fe007801c8 0x200ff803f801e007

def z422 : W := mkw 0x0442010b0c420641 0x001108042c310819 0x000000000c000e00 0x0000000000300038

def z423 : W := mkw 0xfbb5bed452806820 0x13eed6fb514a01a0 0xfffffffe7380701f 0xfbfffffff9ce01c0

def z424 : W := mkw 0xeea6736788038489 0x03ba99cd9e200e12 0xcc867b6780070002 0x173219ed9e001c00

def z425 : W := mkw 0xeaac000063340000 0x23aab000018cd000 0xfffe000073b8000f 0xebfff80001cee000

def z426 : W := mkw 0xac6e00014f520000 0x22b1b800053d4800 0x3f7e00000ff8002d 0xe8fdf800003fe000

def z427 : W := mkw 0x5391dcf0b02dd19c 0x054e4773c2c0b746 0xf3f9fcf9f07ff1ff 0xffcfe7f3e7c1ffc7

def z428 : W := mkw 0x1019041001902802 0x08406410400640a0 0x3038000003800000 0x40c0e000000e0000

def z429 : W := mkw 0xffb5ffd5da00c420 0x13fed7ff57680310 0xfffffffff000001f 0xf7ffffffffc00000

def z430 : W := mkw 0x43c8d8e0b57dd19c 0x050f236382d5f746 0xf3f9f8e1fffff1ff 0xffcfe7e387ffffc7

def z431 : W := mkw 0xfab5365400000000 0x03ead4d950000000 0xfcfe7f7e00000006 0x53f3f9fdf8000000

def z432 : W := mkw 0x43b4d8f4b02dd19c 0x050ed363d2c0b746 0xc3fff8fff07ff1fb 0xbf0fffe3ffc1ffc7

def z433 : W := mkw 0xfffff7ffef7786c9 0x23ffffdfffbdde1b 0xffffffffffff8fff 0xfffffffffffffe3f

def z434 : W := mkw 0x4780d9e1faadfdbc 0x151e036787eab7f6 0xc381f8e1fffffffb 0xbf0e07e387ffffff

def z435 : W := mkw 0x044200010c420000 0x0011080004310800 0x0cc647ff8c47003e 0x9433191ffe311c00

def z436 : W := mkw 0x438090c020240000 0x010e024300809000 0xc381f8e1f07f003b 0xbf0e07e387c1fc00

def z437 : W := mkw 0xffb5ffd5da80ec20 0x13fed7ff576a03b0 0xff39ff01ff80fe37 0xfffce7fc07fe03f8

def z438 : W := mkw 0xbc496f09dfd8ff72 0x1af125bc277f63fd 0xfc01ff01fff8fff7 0xdff007fc07ffe3ff

def z439 : W := mkw 0x438090c0202c1114 0x050e02430080b044 0x0300000000380000 0x200c00000000e000

def z440 : W := mkw 0x43b490d400000000 0x010ed24350000000 0x0ffe47fe0000001e 0xb03ff91ff8000000

def z441 : W := mkw 0xfead6f01fbb4ec20 0x33fab5bc07eed3b0 0xff39ff01ffb8fe37 0xfffce7fc07fee3f8

def z442 : W := mkw 0xac4800014f500000 0x02b12000053d4000 0xff780001fff8002f 0xeffde00007ffe000

def z443 : W := mkw 0x53b594d400000000 0x014ed65350000000 0x33ff84fe0000001d 0xe0cffe13f8000000

def z444 : W := mkw 0xeaee000025760000 0x23abb8000095d800 0xfffe0000007f000f 0xe3fff8000001fc00

def z445 : W := mkw 0x0000002000010088 0x0000000080000402 0x008000e0004701c8 0x0002000380011c07

def z446 : W := mkw 0x47c2d1ebac6f97dd 0x051f0b47aeb1be5f 0x0fc647ff8c7f8ffe 0xb43f191ffe31fe3f

def z447 : W := mkw 0x1059041805d02a42 0x08416410601740a9 0x337804180ff80e2d 0xe8cde010603fe038

def z448 : W := mkw 0x1111849000081110 0x0044461240002044 0x337984980078f1fd 0xe8cde6126001e3c7

def z449 : W := mkw 0x0008000001100000 0x0000200000044000 0x3338000003b80001 0x68cce000000ee000

def z450 : W := mkw 0x53d994d805d83b52 0x094f6653601760ed 0xf3f9fcf80ff8ffff 0xfbcfe7f3e03fe3ff

def z451 : W := mkw 0x044241018c428400 0x0011090406310a10 0x0cc647018c478e3e 0x9433191c06311e38

def z452 : W := mkw 0xebac98c0733c5114 0x27aeb26301ccf144 0xf339b80073b87001 0x6bcce6e001cee1c0

def z453 : W := mkw 0x0048000005500000 0x0001200000154000 0x000000000ff80020 0x08000000003fe000

def z454 : W := mkw 0x1011261400000000 0x0040449850000000 0x0000071e00000000 0x0000001c78000000

def z455 : W := mkw 0xb8016f00d280ec20 0x12e005bc034a03b0 0xf001ff007380fe11 0x5bc007fc01ce03f8

def z456 : W := mkw 0xa824220400000000 0x02a0908810000000 0x0c06030600000000 0x0030180c18000000

def z457 : W := mkw 0xeffe80996f7e1352 0x2bbffa0265bdf84d 0xfffe0099ffff01ef 0xeffff80267fffc07

def z458 : W := mkw 0xeaa4324400000000 0x03aa90c910000000 0xfffe7b660000000f 0xf3fff9ed98000000

def z459 : W := mkw 0x4380d8e09009d19c 0x050e036382402746 0xc381f8e00000f1db 0xb30e07e3800003c7

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x004004980000001c 0x8001001260000000

def z461 : W := mkw 0xfbbd849063bc3912 0x2beef612418ef0e4 0xf339800073b87001 0x6bcce60001cee1c0

def z462 : W := mkw 0xbd59a7994fd83f72 0x1af5669e653f60fd 0x3f7987980ff8fffd 0xe8fde61e603fe3ff

def z463 : W := mkw 0x0000402080018088 0x0000010082000602 0x00000001804781e0 0x0400000006011e07

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c600fe00000008 0x00031803f8000000

def z465 : W := mkw 0x42805860b02dd19c 0x050a016182c0b746 0xc0807861f07ff1e2 0x1f0201e187c1ffc7

def z466 : W := mkw 0x46825963b827c48d 0x051a09658ee09f12 0xcc867b67f0070002 0x173219ed9fc01c00

def z467 : W := mkw 0xac4a00016f760000 0x22b1280005bdd800 0xfc000001ffff0027 0xcff0000007fffc00

def z468 : W := mkw 0x1001040000000000 0x0040041000000000 0x3001840000000015 0xc0c0061000000000

def z469 : W := mkw 0x42805860b025c08c 0x050a016182c09702 0xc081f861f007f033 0x9f0207e187c01fc0

def z470 : W := mkw 0xeeee32456f760000 0x23bbb8c915bdd800 0xfffe7b67ffff002f 0xfffff9ed9ffffc00

def z471 : W := mkw 0xa82c000043100000 0x22a0b000010c4000 0x3038000003800000 0x40c0e000000e0000

def z472 : W := mkw 0x539194d000000000 0x014e465340000000 0xf3f9fcf80000001f 0xf3cfe7f3e0000000

def z473 : W := mkw 0x0000000800000240 0x0000000020000009 0x0000049800008fd0 0x000000126000023f

def z474 : W := mkw 0x040049019800c400 0x0010012406600310 0xcc01ff01fc00fe37 0x9f3007fc07f003f8

def z475 : W := mkw 0x1151849804c83b52 0x08454612601320ed 0x004184980c40fffc 0x80010612603103ff

def z476 : W := mkw 0x1111849000000000 0x0044461240000000 0x0001849800000010 0x0000061260000000

def z477 : W := mkw 0x42805860b025c08c 0x050a016182c09702 0xc3807861f07f002b 0xbf0e01e187c1fc00

def z478 : W := mkw 0xbc3527154a802c20 0x12f0d49c552a00b0 0x3c7e071e0f800e04 0x40f1f81c783e0038

def z479 : W := mkw 0x0040000804400240 0x0001000020110009 0x004004180c000e04 0x0001001060300038

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0x000180000000f031 0x88000600000003c0

def z481 : W := mkw 0xeea600016a260000 0x23ba980005a89800 0xfc860001ff870027 0xcff2180007fe1c00

def z482 : W := mkw 0xb801260000802800 0x02e00498000200a0 0xfc01ff000f80fe37 0xdbf007fc003e03f8

def z483 : W := mkw 0xbc0126014a000000 0x02f0049805280000 0xfc01ff01ff800037 0xdff007fc07fe0000

def z484 : W := mkw 0xb801260000000000 0x02e0049800000000 0xf001b80000000001 0x43c006e000000000

def z485 : W := mkw 0xeea64123ea278489 0x23ba99048fa89e12 0xcc864367f0070002 0x1732190d9fc01c00

def z486 : W := mkw 0xa800220000000000 0x02a0008800000000 0xcc007b0000000002 0x133001ec00000000

def z487 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xffffb8000000000f 0xe3fffee000000000

def z488 : W := mkw 0x0442010b0c420641 0x001108042c310819 0x0c46079e0c408ffc 0x8031181e7831023f

def z489 : W := mkw 0xfeff26156f760000 0x23fbfc9855bdd800 0xfffe071fffff002f 0xeffff81c7ffffc00

def z490 : W := mkw 0x0402412388038489 0x001009048e200e12 0x0000000180070000 0x0400000006001c00

def z491 : W := mkw 0xff81ffc1faacfd34 0x17fe07ff07eab3f4 0xff01ff01ffb8fe37 0xfffc07fc07fee3f8

def z492 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc007f01ff800e06 0x57f001fc07fe0038

def z493 : W := mkw 0xb919ae9053987932 0x1ae466ba414e61e4 0xf339b80073b87001 0x6bcce6e001cee1c0

def z494 : W := mkw 0xb8016e009000c000 0x02e005b802400300 0xfc01ff01f000f037 0xdff007fc07c003c0

def z495 : W := mkw 0xac42412bce4386c9 0x02b10904af390e1b 0xfcc647ffffc78fff 0xdff3191fffff1e3f

def z496 : W := mkw 0xeaa4324400000000 0x03aa90c910000000 0xc000380000000000 0x030000e000000000

def z497 : W := mkw 0xbc436f01dec2ec20 0x12f10dbc077b0bb0 0xfcc7ff01ffc7fe3f 0xdff31ffc07ff1ff8

def z498 : W := mkw 0xb835261400000000 0x02e0d49850000000 0xfc7fff1e00000017 0xd3f1fffc78000000

def z499 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x307984980f80ffd4 0x40c1e612603e03ff

def z500 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc643ff804701ca 0x1433190ffe011c07

def z501 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x00c600ff8c478fe8 0x04031803fe311e3f

def z502 : W := mkw 0xeeee412bef7786c9 0x23bbb904afbdde1b 0xfffe0001ffff8fef 0xeffff80007fffe3f

def z503 : W := mkw 0x1001040000802800 0x00400410000200a0 0x300004000f800e04 0x40c00010003e0038

def z504 : W := mkw 0x000058609001c08c 0x0400016182400702 0x0000786000000000 0x100001e180000000

def z505 : W := mkw 0x010090c000000000 0x0004024300000000 0x0001f8e000000010 0x100007e380000000

def z506 : W := mkw 0x0100d8e09009d19c 0x0404036382402746 0xc001f8e1f000f1f3 0x9f0007e387c003c7

def z507 : W := mkw 0xeeee4901fff6ec20 0x33bbb92407ffdbb0 0xfffe0001fffffe2f 0xeffff80007fffff8

def z508 : W := mkw 0x0042000004420000 0x0001080000110800 0x00c6000000470008 0x0003180000011c00

def z509 : W := mkw 0xfbb5849000000000 0x03eed61240000000 0xffff84980000001f 0xe3fffe1260000000

def z510 : W := mkw 0x0042402a844382c9 0x00010900aa110e0b 0x00c640ff804781fa 0x94031903fe011e07

def z511 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z512 : W := mkw 0x0442492bbc6fd7dd 0x04110924aef1bf5f 0x0cc647fffc7ffffe 0x9c33191ffff1ffff

def z513 : W := mkw 0x53ff849825fe3b52 0x294ffe126097f8ed 0x33ff84980ffffffd 0xe8cffe12603fffff

def z514 : W := mkw 0xfeef26016f760000 0x23fbbc9805bdd800 0xffffff01ffff003f 0xfffffffc07fffc00

def z515 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xff7e00007fb80005 0x6bfdf80001fee000

def z516 : W := mkw 0x47c2d8e1bc6fd19c 0x051f0b6386f1bf46 0xcfc7f8e1fc7ff1ff 0xbf3f1fe387f1ffc7

def z517 : W := mkw 0x43fe8098257e1352 0x290ffa026095f84d 0x03fe0098007f01c8 0x200ff8026001fc07

def z518 : W := mkw 0x1111b6d400000000 0x004446db50000000 0x3379fffe0000001d 0xf0cde7fff8000000

def z519 : W := mkw 0xfffffef5ff7fd19c 0x27fffffbd7fdff46 0xfffffffffffff1ff 0xffffffffffffffc7

def z520 : W := mkw 0x00484828b5fdfbde 0x0c012120a2d7f7ef 0x00000001ffffffe0 0x0c00000007ffffff

def z521 : W := mkw 0x47c2d1eb8c4386c9 0x011f0b47ae310e1b 0xcfc7ffff8c478fff 0xb73f1ffffe311e3f

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000018047002a 0x8402000006011c00

def z523 : W := mkw 0x53d9849825fc3b52 0x094f66126097f0ed 0xf3f98499ffffffff 0xefcfe61267ffffff

def z524 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0x0381f8e0007ff1d8 0x300e07e38001ffc7

def z525 : W := mkw 0x438090c000000000 0x010e024300000000 0xc301b80000000001 0x230c06e000000000

def z526 : W := mkw 0x0048000005500000 0x0001200000154000 0x0378000000780008 0x200de0000001e000

def z527 : W := mkw 0x040000014a000000 0x0010000005280000 0x00000001ff800020 0x0c00000007fe0000

def z528 : W := mkw 0xac006b01da00c420 0x12b001ac07680310 0xcc007f01fc008e36 0x973001fc07f00238

def z529 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xf3ffb8fe00000009 0x63cffee3f8000000

def z530 : W := mkw 0xfeef2e017ff66820 0x33fbbcb805ffd9a0 0xffffb801ffff702f 0xeffffee007fffdc0

def z531 : W := mkw 0x0000412a800186c9 0x00000104aa00061b 0x0cc647fe00008fde 0x9033191ff800023f

def z532 : W := mkw 0x43c290ea246f13dd 0x050f0a43a891bc4f 0x03c600fe007f01c8 0x200f1803f801fc07

def z533 : W := mkw 0x155b84996ffe3b52 0x28556e1265bff8ed 0x33798499fffffffd 0xeccde61267ffffff

def z534 : W := mkw 0x0000402080018088 0x0000010082000602 0x000040e0000081d0 0x1000010380000207

def z535 : W := mkw 0x0000080010004000 0x0000002000400100 0xc001b80070007001 0x0b0006e001c001c0

def z536 : W := mkw 0x0442002b0c4302c9 0x00110800ac310c0b 0x0cc600ff8c4701ee 0x84331803fe311c07

def z537 : W := mkw 0xbd11ffd5da80ec20 0x12f447ff576a03b0 0xfc01ffffff80fe37 0xdff007fffffe03f8

def z538 : W := mkw 0xeaee000067760000 0x23abb800019dd800 0xf3fe000073ff0009 0x6bcff80001cffc00

def z539 : W := mkw 0xeeee6b01ff76c420 0x33bbb9ac07fddb10 0xfffe7b01ffff002f 0xfffff9ec07fffc00

def z540 : W := mkw 0xeea47b45da00c420 0x13ba91ed17680310 0xcc867b67f0000002 0x173219ed9fc00000

def z541 : W := mkw 0x46ee412bad7786c9 0x211bb904aeb5de1b 0x0ffe47ff8c7f8ffe 0xb43ff91ffe31fe3f

def z542 : W := mkw 0xffd9fff9fffdfffe 0x1fff67ffe7fff7ff 0xfff9fff9ffffffff 0xffffe7ffe7ffffff

def z543 : W := mkw 0x43b490d400000000 0x010ed24350000000 0x0338000000000000 0x200ce00000000000

def z544 : W := mkw 0xb959ae9857d87b72 0x1ae566ba615f61ed 0xf379bc987ff8fffd 0xebcde6f261ffe3ff

def z545 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xcffe0001f07f000a 0x273ff80007c1fc00

def z546 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc600018c478fee 0x8433180006311e3f

def z547 : W := mkw 0xeaa4000062240000 0x23aa900001889000 0xc000000070000000 0x0300000001c00000

def z548 : W := mkw 0x46c200012c660000 0x011b080004b19800 0xcfc60001fc7f002f 0xaf3f180007f1fc00

def z549 : W := mkw 0xac2600014a020000 0x22b0980005280800 0x0c06000000000000 0x0030180000000000

def z550 : W := mkw 0x1111b6dc00883b52 0x084446db700220ed 0x0001fffe0000ffd0 0x100007fff80003ff

def z551 : W := mkw 0xbc0127014a802c20 0x12f0049c052a00b0 0x3c0187000f80fe35 0xc8f0061c003e03f8

def z552 : W := mkw 0x43808080202c1110 0x010e02020080b044 0xc3818081f07ff1fb 0xaf0e060207c1ffc7

def z553 : W := mkw 0x5391b6d400000000 0x014e46db50000000 0xc381fffe0000001b 0xb30e07fff8000000

def z554 : W := mkw 0x044a00010d520000 0x0011280004354800 0x3ffe00018fff002f 0xecfff800063ffc00

def z555 : W := mkw 0xac0023014a000420 0x12b0008c05280010 0x0c00030000000000 0x0030000c00000000

def z556 : W := mkw 0xbc0104014a802800 0x02f00410052a00a0 0xfc018401ff80fe37 0xcff0061007fe03f8

def z557 : W := mkw 0xb87d261c05d02a42 0x0ae1f498701740a9 0x3c7e071e0f800e04 0x40f1f81c783e0038

def z558 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x337804980ff80fcc 0x60cde012603fe03f

def z559 : W := mkw 0x43b490d400000000 0x010ed24350000000 0xc3fff8fe0000001b 0xb30fffe3f8000000

def z560 : W := mkw 0x0000412280018489 0x000001048a000612 0x0000436600000000 0x1000010d98000000

def z561 : W := mkw 0xac0000014a000000 0x02b0000005280000 0xcc000001f0000002 0x0730000007c00000

def z562 : W := mkw 0x0442492bdec3eee9 0x10110924af7b0fbb 0x0cc647ffffc7fffe 0x9c33191fffff1fff

def z563 : W := mkw 0x0042002a044302c9 0x00010800a8110c0b 0x0cc647fe004701de 0x9033191ff8011c07

def z564 : W := mkw 0x57dbddfbbdffffdf 0x0d5f6f77eef7ffff 0xffffffffffffffff 0xffffffffffffffff

def z565 : W := mkw 0x0042002a044302c9 0x00010800a8110c0b 0x00c604fe0c478ffc 0x80031813f8311e3f

def z566 : W := mkw 0xeba4fae4b02dd19c 0x07ae93eb92c0b746 0xcf87fbe7f07ff1fb 0xbf3e1fef9fc1ffc7

def z567 : W := mkw 0x42ee000025760000 0x210bb8000095d800 0xc3fe0001f07f002b 0xaf0ff80007c1fc00

def z568 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xffbffb6600000003 0x73feffed98000000

def z569 : W := mkw 0xeeee5861ff77c08c 0x27bbb96187fddf02 0xfffe7861ffff002f 0xfffff9e187fffc00

def z570 : W := mkw 0xac0000014a000000 0x02b0000005280000 0x3c0000000f800004 0x40f00000003e0000

def z571 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0c46071f8c478fe4 0x0431181c7e311e3f

def z572 : W := mkw 0xfea56f01da80ec20 0x13fa95bc076a03b0 0xffffff01ff80fe3f 0xfffffffc07fe03f8

def z573 : W := mkw 0x1553f7ff8c4386c9 0x00554fdffe310e1b 0x0cc7ffff8c478ffe 0x94331ffffe311e3f

def z574 : W := mkw 0xfffff7ff8ddbbfdb 0x0bffffdffe376eff 0xffffffff8fffffff 0xfffffffffe3fffff

def z575 : W := mkw 0xb935a69400000000 0x02e4d69a50000000 0x3f7f879e0000001d 0xe0fdfe1e78000000

def z576 : W := mkw 0x0000080052806820 0x10000020014a01a0 0x0000000073807000 0x0800000001ce01c0

def z577 : W := mkw 0xbc496f01dfd0ec20 0x12f125bc077f43b0 0xff79ff01fff8fe3f 0xfffde7fc07ffe3f8

def z578 : W := mkw 0xb959a69805d83b52 0x0ae5669a601760ed 0xff79ff980ff8ffff 0xfbfde7fe603fe3ff

def z579 : W := mkw 0xfbf5b6dc04400240 0x03efd6db70110009 0xfffffffe0c408fff 0xf3fffffff831023f

def z580 : W := mkw 0x438098e0302d519c 0x050e026380c0b546 0xc381b8e0707f71c9 0x2b0e06e381c1fdc7

def z581 : W := mkw 0xfbfdb6dc05d83b52 0x0beff6db701760ed 0xf379bc980ff8fffd 0xebcde6f2603fe3ff

def z582 : W := mkw 0x43d890f8257d13de 0x0d0f6243e095f44f 0x03f800f8007f01c8 0x200fe003e001fc07

def z583 : W := mkw 0x145b453b8dd3aecb 0x08516d14ee374ebb 0x3cfe47ff8fc78ffe 0xd4f3f91ffe3f1e3f

def z584 : W := mkw 0x428010602025008c 0x050a004180809402 0x0080006000070000 0x0002000180001c00

def z585 : W := mkw 0xffffef99fffeff72 0x3bffffbe67fffbfd 0xffffff99ffffffff 0xfffffffe67ffffff

def z586 : W := mkw 0xff81ffc1da80ec20 0x13fe07ff076a03b0 0xff81ffe1ff80fe3f 0xfffe07ff87fe03f8

def z587 : W := mkw 0x43c0d8e8b46dd3dc 0x050f0363a2d1b74f 0xc3c1fcf9fc7fffff 0xbf0f07f3e7f1ffff

def z588 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x337984180fb87e05 0x68cde610603ee1f8

def z589 : W := mkw 0xfeef6f2bfff7eee9 0x33fbbdbcafffdfbb 0xffffffffffffffff 0xffffffffffffffff

def z590 : W := mkw 0x438098c0302c5114 0x050e026300c0b144 0xc381f8e07038701b 0xbb0e07e381c0e1c0

def z591 : W := mkw 0x055ac1bb8d5b97db 0x08156b06ee356e5f 0x0ffe47ff8c7f8ffe 0xb43ff91ffe31fe3f

def z592 : W := mkw 0xbc6f6f01dfd2ec20 0x32f1bdbc077f4bb0 0xfc7fff01ff80fe37 0xdff1fffc07fe03f8

def z593 : W := mkw 0x10016f009080ec20 0x104005bc024203b0 0xc001ff01f000fe33 0x9f0007fc07c003f8

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x008040e00000001a 0x9002010380000000

def z595 : W := mkw 0xfff7ffffbc6fd7dd 0x07ffdffffef1bf5f 0xfffffffffc7fffff 0xfffffffffff1ffff

def z596 : W := mkw 0x04484909dfd8ff72 0x18112124277f63fd 0x00000001fff8ffe0 0x0c00000007ffe3ff

def z597 : W := mkw 0x42804820b02dd19c 0x050a012082c0b746 0xc3800001f07ff1eb 0xaf0e000007c1ffc7

def z598 : W := mkw 0x1553c5bb8ccbbfdb 0x08554f16ee332eff 0x0cc7c7ff8c47fffe 0x94331f1ffe311fff

def z599 : W := mkw 0x1111fef49009d19c 0x044447fbd2402746 0x0001fffe0000f1d0 0x100007fff80003c7

def z600 : W := mkw 0xeeee4101ef768400 0x23bbb90407bdda10 0xfffe4701ffff8e3f 0xfffff91c07fffe38

def z601 : W := mkw 0x0400410188008400 0x0010010406200210 0x000000018c008e20 0x0400000006300238

def z602 : W := mkw 0xb911a69000000000 0x02e4469a40000000 0xff79ff980000001f 0xf3fde7fe60000000

def z603 : W := mkw 0x14014d01da80ec20 0x10500534076a03b0 0x30018401ff80fe35 0xccc0061007fe03f8

def z604 : W := mkw 0xac4200014e420000 0x02b1080005390800 0xfcc60001ffc7002f 0xcff3180007ff1c00

def z605 : W := mkw 0x044041098c408640 0x0011010426310219 0x0c4047998c408ffe 0x9431011e6631023f

def z606 : W := mkw 0xffffb6d54f520000 0x23fffedb553d4800 0xfffffffe0f80001f 0xf3fffffff83e0000

def z607 : W := mkw 0x0110809000000000 0x0004420240000000 0x0378009800000008 0x200de00260000000

def z608 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xcc860001ffff0022 0x0f32180007fffc00

def z609 : W := mkw 0x0140808804481350 0x000502022011204d 0x034184980c78fffd 0xa80d06126031e3ff

def z610 : W := mkw 0xeeee002b6f7702c9 0x23bbb800adbddc0b 0xfffe00ffffff01ef 0xeffff803fffffc07

def z611 : W := mkw 0xebb490d400000000 0x03aed24350000000 0xfffe00fe0000000f 0xe3fff803f8000000

def z612 : W := mkw 0xa8002a0052004020 0x12a000a801480100 0xc000380070000000 0x030000e001c00000

def z613 : W := mkw 0x1001040000802800 0x00400410000200a0 0x3001800003807001 0x48c00600000e01c0

def z614 : W := mkw 0x0442492bdec3eee9 0x10110924af7b0fbb 0x00000001ffc7ffe0 0x0c00000007ff1fff

def z615 : W := mkw 0xfffdffdddfd8ff72 0x1bfff7ff777f63fd 0xfffffffffff8ffff 0xffffffffffffe3ff

def z616 : W := mkw 0xbd5984994fd83b52 0x0af56612653f60ed 0xff798499fff8ffff 0xeffde61267ffe3ff

def z617 : W := mkw 0x0048000005500000 0x0001200000154000 0x307800000f800004 0x40c1e000003e0000

def z618 : W := mkw 0xbd19ef91db98fd32 0x1af467be476e63f4 0xff39ff01ffb8fe37 0xfffce7fc07fee3f8

def z619 : W := mkw 0xa800000000000000 0x02a0000000000000 0xfc00000000000007 0xc3f0000000000000

def z620 : W := mkw 0x0000410080008400 0x0000010402000210 0x0000470000008e10 0x1000011c00000238

def z621 : W := mkw 0x1119849001983912 0x08446612400660e4 0x3379849803b8701d 0xe8cde612600ee1c0

def z622 : W := mkw 0x040200016a260000 0x2010080005a89800 0x00000001f0070000 0x0400000007c01c00

def z623 : W := mkw 0x0442010b0c420641 0x001108042c310819 0x0cc6071f8c470e2e 0x8433181c7e311c38

def z624 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0x3c000701ff80fe24 0x4cf0001c07fe03f8

def z625 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x008040e18c478ffa 0x9402010386311e3f

def z626 : W := mkw 0xeea65861fa27c08c 0x27ba996187e89f02 0xcc867861f0070002 0x173219e187c01c00

def z627 : W := mkw 0x1159ef9895d8ff72 0x184567be625763fd 0x3379ff980ff8fffd 0xf8cde7fe603fe3ff

def z628 : W := mkw 0x015a80ba055b13db 0x08056a02e8156c4f 0x03fe00fe007f01c8 0x200ff803f801fc07

def z629 : W := mkw 0x0100d8e09009d19c 0x0404036382402746 0x0301f8e00078f1f9 0xb80c07e38001e3c7

def z630 : W := mkw 0xeee6412b8c4386c9 0x03bb9904ae310e1b 0xfffe47ff8c478fff 0xf7fff91ffe311e3f

def z631 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01fb01f3807003 0x5ff007ec07ce01c0

def z632 : W := mkw 0xfab5261400000000 0x03ead49850000000 0xfffe071e0000000f 0xe3fff81c78000000

def z633 : W := mkw 0x145b051b0dd22e43 0x08516c146c3748b9 0x3c7e071e0f800e04 0x40f1f81c783e0038

def z634 : W := mkw 0x42a4000000000000 0x010a900000000000 0x03fe000000000008 0x200ff80000000000

def z635 : W := mkw 0x42ac000021340000 0x210ab0000084d000 0x0338000000380000 0x200ce0000000e000

def z636 : W := mkw 0xbc436f2bdec3eee9 0x12f10dbcaf7b0fbb 0xfc01ff01ffc7fff7 0xdff007fc07ff1fff

def z637 : W := mkw 0x4280000020240000 0x010a000000809000 0xc0800001f0070002 0x0702000007c01c00

def z638 : W := mkw 0xeeee4801ff76c000 0x23bbb92007fddb00 0xfffff801fffff03f 0xffffffe007ffffc0

def z639 : W := mkw 0x46ca00016f760000 0x211b280005bdd800 0xc3800001ffff002b 0xaf0e000007fffc00

def z640 : W := mkw 0x0100d8e0b02dd19c 0x0404036382c0b746 0x0001f8e1f07ff1f0 0x1c0007e387c1ffc7

def z641 : W := mkw 0x1111849800883b52 0x08444612600220ed 0x337984980000ffdd 0xe0cde612600003ff

def z642 : W := mkw 0x0402010308020401 0x001008040c200810 0x0c06030600000000 0x0030180c18000000

def z643 : W := mkw 0xffb5f7d588008400 0x03fed7df56200210 0xffffffff8c008e3f 0xf7fffffffe300238

def z644 : W := mkw 0xbc016f21faadfdbc 0x16f005bc87eab7f6 0xfc01ff01fffffff7 0xdff007fc07ffffff

def z645 : W := mkw 0x1111c5ba8089bfdb 0x08444716ea0226ff 0x0001c7fe0000ffd0 0x1000071ff80003ff

def z646 : W := mkw 0x1559c5998dd8bf52 0x08556716663762fd 0x3f79c7998ff8ffff 0xfcfde71e663fe3ff

def z647 : W := mkw 0x1119849001983912 0x08446612400660e4 0x333984000fb8fe35 0xe8cce610003ee3f8

def z648 : W := mkw 0xfbb5b6dc00883b52 0x0beed6db700220ed 0xfffffffe0000ffdf 0xf3fffffff80003ff

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0xc001f80000000013 0x930007e000000000

def z650 : W := mkw 0x43c2d8eab46fd3dd 0x050f0b63aad1bf4f 0xc3c7f8fff07ff1fb 0xbf0f1fe3ffc1ffc7

def z651 : W := mkw 0x00006b009000c420 0x100001ac02400310 0x00007b0000000000 0x100001ec00000000

def z652 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x000047ff8c478ff0 0x1400011ffe311e3f

def z653 : W := mkw 0xfb81b6c000000000 0x03ee06db00000000 0xff81ffe00000001f 0xf3fe07ff80000000

def z654 : W := mkw 0x000048009000c000 0x0000012002400300 0x00000001f000f020 0x0c00000007c003c0

def z655 : W := mkw 0xfb81bec072ac7934 0x17ee06fb01cab1e4 0xf301b80073b87001 0x6bcc06e001cee1c0

def z656 : W := mkw 0x438098c0302c5114 0x050e026300c0b144 0xc301b8807078f1f9 0xab0c06e201c1e3c7

def z657 : W := mkw 0xffb7b6d56a260000 0x23fededb55a89800 0xfffffffff007001f 0xf7ffffffffc01c00

def z658 : W := mkw 0xbd01ffe1da89fdbc 0x16f407ff876a27f6 0xfc01ffe1ff80fff7 0xdff007ff87fe03ff

def z659 : W := mkw 0x0040000804400240 0x0001000020110009 0x00400098004001c8 0x0001000260010007

def z660 : W := mkw 0xac6e010b4f520641 0x22b1b8042d3d4819 0x3c7e071e0f800e04 0x40f1f81c783e0038

def z661 : W := mkw 0x14016f019880ec20 0x105005bc066203b0 0x0c01ff018c00fe36 0x943007fc063003f8

def z662 : W := mkw 0x438090e0202d119c 0x050e02438080b446 0x038180e0007ff1f9 0xa80e06038001ffc7

def z663 : W := mkw 0x0100808000081110 0x0004020200002044 0x03000080007801c8 0x200c00020001e007

def z664 : W := mkw 0x0402412388038489 0x001009048e200e12 0x0c8647678c078e36 0x9432191d9e301e38

def z665 : W := mkw 0x00000020202d119c 0x040000008080b446 0x00000000007f01c0 0x000000000001fc07

def z666 : W := mkw 0x044a00014f520000 0x20112800053d4800 0x000000000f800000 0x00000000003e0000

def z667 : W := mkw 0x14016f01da80ec20 0x105005bc076a03b0 0x0001ff01ff80fe30 0x1c0007fc07fe03f8

def z668 : W := mkw 0x1159c5ba85d9bfdb 0x08456716ea1766ff 0x3379c7fe0ff8fffd 0xf8cde71ff83fe3ff

def z669 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x3379809803f871c9 0x68cde602600fe1c7

def z670 : W := mkw 0x1159849005500000 0x0045661240154000 0x337984980ff8003d 0xe8cde612603fe000

def z671 : W := mkw 0xefeed9ebff7fd7dd 0x27bfbb67affdff5f 0xffffffffffffffff 0xffffffffffffffff

def z672 : W := mkw 0x1443452b8cc3aec9 0x00510d14ae330ebb 0x3cc7c7ff8fc7ffff 0xdcf31f1ffe3f1fff

def z673 : W := mkw 0x0040000804400240 0x0001000020110009 0x0cc647fe0c408ffe 0x9033191ff831023f

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cc600000000000e 0x8033180000000000

def z675 : W := mkw 0xbc0127014a802c20 0x12f0049c052a00b0 0xfc000701ff800e27 0xcff0001c07fe0038

def z676 : W := mkw 0xfbffb6d425760000 0x23effedb5095d800 0xfffffffe007f001f 0xf3fffffff801fc00

def z677 : W := mkw 0x5391fef4b02dd19c 0x054e47fbd2c0b746 0xc381fffff07ff1fb 0xbf0e07ffffc1ffc7

def z678 : W := mkw 0xebacd8e0f33dd19c 0x27aeb36383ccf746 0xf3b9f8e1f3fff1fb 0xffcee7e387cfffc7

def z679 : W := mkw 0x0402412388038489 0x001009048e200e12 0x0c8643e7804781fa 0x9432190f9e011e07

def z680 : W := mkw 0x00404028844182c8 0x00010100a211060b 0x00c044f98c478ffe 0x94030113e6311e3f

def z681 : W := mkw 0x010090e00009119c 0x0404024380002446 0x000000e0000001c0 0x0000000380000007

def z682 : W := mkw 0xac6e00016f760000 0x22b1b80005bdd800 0x3c7e0001ffff0024 0x4cf1f80007fffc00

def z683 : W := mkw 0xfff7b7df0c420641 0x03ffdedf7c310819 0xfffffffe0c000e1f 0xf3fffffff8300038

def z684 : W := mkw 0xac026b23da03c4a9 0x12b009ac8f680f12 0xcc867b67f0070002 0x173219ed9fc01c00

def z685 : W := mkw 0x1151849804400240 0x0045461260110009 0x337984980c408ffd 0xe0cde6126031023f

def z686 : W := mkw 0x42804020a0258088 0x010a010082809602 0xc38040e1f07f81fb 0xbf0e010387c1fe07

def z687 : W := mkw 0x46c2596bbc67c6cd 0x051b0965aef19f1b 0xccc67ffffc478ffe 0x973319fffff11e3f

def z688 : W := mkw 0xbc77271f0c420641 0x02f1dc9c7c310819 0x3c7e071e0c000e04 0x40f1f81c78300038

def z689 : W := mkw 0x040001014a802c20 0x10100004052a00b0 0x000000000f800e00 0x00000000003e0038

def z690 : W := mkw 0xac004801da00c000 0x02b0012007680300 0xfc01f801ff80f037 0xdff007e007fe03c0

def z691 : W := mkw 0x1159ccb8b5fdfbde 0x0c456732e2d7f7ef 0x33798499fffffffd 0xeccde61267ffffff

def z692 : W := mkw 0xb8016e00d280e820 0x12e005b8034a03a0 0xf001f801f380f033 0xdfc007e007ce03c0

def z693 : W := mkw 0x00000800302c5114 0x0400002000c0b144 0x0000000070387000 0x0800000001c0e1c0

def z694 : W := mkw 0xfbbdb6d463340000 0x23eef6db518cd000 0xf339b80073b80001 0x6bcce6e001cee000

def z695 : W := mkw 0x42805860b025c08c 0x050a016182c09702 0xc08078e1f04781fa 0x970201e387c11e07

def z696 : W := mkw 0xeaa4324400000000 0x03aa90c910000000 0xccc67ffe0000001e 0x933319fff8000000

def z697 : W := mkw 0x0048000805d83b52 0x08012000201760ed 0x004004980ff8fffc 0x88010012603fe3ff

def z698 : W := mkw 0xeea400014a000000 0x03ba900005280000 0xfffe0001ff80002f 0xeffff80007fe0000

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c46071e00000004 0x0031181c78000000

def z700 : W := mkw 0xb835261400000000 0x02e0d49850000000 0x3cfe47fe0000001e 0xd0f3f91ff8000000

def z701 : W := mkw 0x43d8d8f8b57dd3de 0x0d0f6363e2d5f74f 0xc3f9f8f9f07ff1fb 0xbf0fe7e3e7c1ffc7

def z702 : W := mkw 0x42ee000025760000 0x210bb8000095d800 0x33fe00000fff002d 0xe8cff800003ffc00

def z703 : W := mkw 0xeee600010c420000 0x03bb980004310800 0xfffe00018c47002f 0xe7fff80006311c00

def z704 : W := mkw 0x044a00096ffe3b52 0x2811280025bff8ed 0x00000001ffffffe0 0x0c00000007ffffff

def z705 : W := mkw 0x1059041805d83b52 0x08416410601760ed 0x307804180ff8ffe4 0x48c1e010603fe3ff

def z706 : W := mkw 0x155b859b0dda3f53 0x08556e166c3768fd 0x3f7f879e0ff8fffd 0xe8fdfe1e783fe3ff

def z707 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01ff01ff807e07 0x5ff007fc07fe01f8

def z708 : W := mkw 0xeba490c000000000 0x03ae924300000000 0xfffffffe0000001f 0xf3fffffff8000000

def z709 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc381b801f07ff1eb 0xaf0e06e007c1ffc7

def z710 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0xccc7ffff8c478fff 0x97331ffffe311e3f

def z711 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfffffffe0c008e3f 0xf3fffffff8300238

def z712 : W := mkw 0xb8432e2a56c36ae9 0x12e10cb8a95b0dab 0xf0c7b8fe73c771c9 0x4bc31ee3f9cf1dc7

def z713 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xff7ffffe00000015 0x73fdfffff8000000

def z714 : W := mkw 0xeaac000063340000 0x23aab000018cd000 0xfffe0001f3ff002f 0xeffff80007cffc00

def z715 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01ffffff80fe37 0xdff007fffffe03f8

def z716 : W := mkw 0xad58eb99df58d772 0x1ab563ae677d635d 0xcf787b99f07801ca 0x373de1ee67c1e007

def z717 : W := mkw 0x46ee00016f760000 0x211bb80005bdd800 0x33fe0001ffff002d 0xeccff80007fffc00

def z718 : W := mkw 0xeaac000063340000 0x23aab000018cd000 0xf3380001f3ff0021 0x6fcce00007cffc00

def z719 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfffffffe004081ff 0xf3fffffff8010207

def z720 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe071fffff002f 0xeffff81c7ffffc00

def z721 : W := mkw 0x1119849801983b52 0x08446612600660ed 0x333984980fb8fff5 0xe8cce612603ee3ff

def z722 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x3cc647ff8fc78fff 0xdcf3191ffe3f1e3f

def z723 : W := mkw 0xeeee22016f760000 0x23bbb88805bdd800 0xfffe7b01ffff002f 0xfffff9ec07fffc00

def z724 : W := mkw 0xeeee010b6f760641 0x23bbb8042dbdd819 0xfffe47ffffff0e3f 0xfffff91ffffffc38

def z725 : W := mkw 0x0442412bce4386c9 0x00110904af390e1b 0x0cc647ffffc78ffe 0x9c33191fffff1e3f

def z726 : W := mkw 0xeaee000067760000 0x23abb800019dd800 0xf3fe0001f3ff002b 0xefcff80007cffc00

def z727 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc47ff1fff80fe37 0xdff11ffc7ffe03f8

def z728 : W := mkw 0xff81b7e16aad3dbc 0x17fe06df85aab4f6 0x3f8007e00fff0fcc 0x60fe001f803ffc3f

def z729 : W := mkw 0x1111efba9089fffb 0x184447beea4227ff 0x0001fffe0000ffd0 0x100007fff80003ff

def z730 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xff380001ffff0027 0xeffce00007fffc00

def z731 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc7c7ff8c47ffff 0x9c331f1ffe311fff

def z732 : W := mkw 0x115b849a05da3b53 0x08456e12681768ed 0x337f849e0ff8fffd 0xe8cdfe12783fe3ff

def z733 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x337804980ff8ffec 0x68cde012603fe3ff

def z734 : W := mkw 0x0148808805d83b52 0x08052202201760ed 0x337980800ff8fffd 0xe8cde602003fe3ff

def z735 : W := mkw 0x0000412a800186c9 0x00000104aa00061b 0x0cc647ff80478ffe 0x9433191ffe011e3f

def z736 : W := mkw 0xeea400016a240000 0x03ba900005a89000 0xfffe0001ffff002f 0xeffff80007fffc00

def z737 : W := mkw 0x47b4d9d5da80ec20 0x111ed367576a03b0 0x03fe00ffff80fe28 0x2c0ff803fffe03f8

def z738 : W := mkw 0x1119849001983912 0x08446612400660e4 0x333984800ff8fffd 0xe8cce612003fe3ff

def z739 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01fb01ff80fe23 0x5ff007ec07fe03f8

def z740 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc3c7f8fff07ff1fb 0xbf0f1fe3ffc1ffc7

def z741 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x337980000ff8ffed 0xe8cde600003fe3ff

def z742 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc081f8e1f07ff1f2 0x1f0207e387c1ffc7

def z743 : W := mkw 0xfbbdb6d463bc3912 0x2beef6db518ef0e4 0xf339b80073b87001 0x6bcce6e001cee1c0

def z744 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffff801ffff003f 0xffffffe007fffc00

def z745 : W := mkw 0x155bb6d56f760000 0x20556edb55bdd800 0x0001ffffffff0030 0x1c0007fffffffc00

def z746 : W := mkw 0xfbb5b6d420240000 0x03eed6db50809000 0xfffffffe7038001f 0xfbfffffff9c0e000

def z747 : W := mkw 0x43fc90fc257d13de 0x0d0ff243f095f44f 0x03fe00fe007f01c8 0x200ff803f801fc07

def z748 : W := mkw 0xb935b6d400000000 0x02e4d6db50000000 0xfc7ffffe00000017 0xd3f1fffff8000000

def z749 : W := mkw 0xeaac412ae33586c9 0x23aab104ab8cd61b 0xf33847fe73b88fd1 0x7bcce11ff9cee23f

def z750 : W := mkw 0xfbb5b6d420240000 0x03eed6db50809000 0xfffffffff007001f 0xf7ffffffffc01c00

def z751 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x333984980ff8fff1 0x68cce612603fe3ff

def z752 : W := mkw 0xb8356e34b02dd19c 0x06e0d5b8d2c0b746 0x3c7e071ff07ff1e4 0x4cf1f81c7fc1ffc7

def z753 : W := mkw 0x4390d8f4b02dd19c 0x050e4363d2c0b746 0xc381f8fff07ff1fb 0xbf0e07e3ffc1ffc7

def z754 : W := mkw 0x151bc5b3899bbd9b 0x08546f16ce266ef6 0x3fbfc36783bf7003 0x7cfeff0d9e0efdc0

def z755 : W := mkw 0xbc356f15da80ec20 0x12f0d5bc576a03b0 0xfc39ff01ff80fe37 0xdff0e7fc07fe03f8

def z756 : W := mkw 0x47c299cb3c6e5755 0x051f0a672cf1b95d 0xcf47bf1e7c387e05 0x2b3d1efc79f0e1f8

def z757 : W := mkw 0xfff7f7ff8c4386c9 0x03ffdfdffe310e1b 0xf339b8018c478fe1 0x67cce6e006311e3f

def z758 : W := mkw 0xeea47b65fa25c4ac 0x17ba91ed97e89712 0xcc867b67f0070002 0x173219ed9fc01c00

def z759 : W := mkw 0xeeee00096f760240 0x23bbb80025bdd809 0xfffe0099ffff01ef 0xeffff80267fffc07

def z760 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc81ff01ffc7fe3f 0xdff207fc07ff1ff8

def z761 : W := mkw 0x42ee000025760000 0x210bb8000095d800 0xf3fe0001ffff002f 0xefcff80007fffc00

def z762 : W := mkw 0x14014d019880ec00 0x00500534066203b0 0xfc01ff01ff80fe37 0xdff007fc07fe03f8

def z763 : W := mkw 0xfbb5b6d442802820 0x13eed6db510a00a0 0xfffffffe0380001f 0xf3fffffff80e0000

def z764 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0fc647ff8c7f8fff 0xbc3f191ffe31fe3f

def z765 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xffffff7e00000007 0x73fffffdf8000000

def z766 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xff7e0001ffff0025 0x6ffdf80007fffc00

def z767 : W := mkw 0x4390d8f0b02dd19c 0x050e4363c2c0b746 0xc3f9f8f9f07ff1fb 0xbf0fe7e3e7c1ffc7

def z768 : W := mkw 0xffb784996aae3b52 0x2bfede1265aab8ed 0xcc878499f007ffd2 0x07321e1267c01fff

def z769 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc81ffe1ff80fe3f 0xdff207ff87fe03f8

def z770 : W := mkw 0x52ef6f00b5f6ec20 0x314bbdbc02d7dbb0 0x03ffff00007ffe18 0x300ffffc0001fff8

def z771 : W := mkw 0xfab5365400000000 0x03ead4d950000000 0xfcffff7e00000017 0xd3f3fffdf8000000

def z772 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01bf01ff80fe25 0x4ff006fc07fe03f8

def z773 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe00ffffff002f 0xeffff803fffffc00

def z774 : W := mkw 0x52d95c78b5f5eace 0x0d4b6571e2d7d7ab 0xf0f87c79ff870e06 0x57c3e1f1e7fe1c38

def z775 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfcc7ff01ff80fe3f 0xdff31ffc07fe03f8

def z776 : W := mkw 0xb8016e009080e800 0x02e005b8024203a0 0xfc01ff01ff80fe37 0xdff007fc07fe03f8

def z777 : W := mkw 0x0048000025740000 0x000120000095d000 0x33780001ffff002d 0xeccde00007fffc00

def z778 : W := mkw 0x0148808805581350 0x000522022015604d 0x337984980ff8fffd 0xe8cde612603fe3ff

def z779 : W := mkw 0xb935b6d400000000 0x02e4d6db50000000 0x3cfffffe0000001e 0xd0f3fffff8000000

def z780 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xf3f9f8e1f07ff1ff 0xffcfe7e387c1ffc7

def z781 : W := mkw 0x539194d000000000 0x014e465340000000 0xfffffffe0000001f 0xf3fffffff8000000

def z782 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x333980800ff8fff9 0xe8cce602003fe3ff

def z783 : W := mkw 0xeeae00016b360000 0x23bab80005acd800 0xffbe0001ffbf0027 0xeffef80007fefc00

def z784 : W := mkw 0xeeee000b6f760241 0x23bbb8002dbdd809 0xfffe001fffff002f 0xeffff8007ffffc00

def z785 : W := mkw 0x0402412b880386c9 0x00100904ae200e1b 0x0c8647ff80478ffa 0x9432191ffe011e3f

def z786 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0x3ffffffe0000001c 0x70fffffff8000000

def z787 : W := mkw 0x0442492b9c43c6c9 0x00110924ae710f1b 0x0cc7ffff8c47fffe 0x94331ffffe311fff

def z788 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc607ff8c478fec 0x0433181ffe311e3f

def z789 : W := mkw 0x1149848005d83910 0x00452612001760e4 0x337984800ff8fffd 0xe8cde612003fe3ff

def z790 : W := mkw 0xad6ed8e1df5bd19c 0x26b5bb63877d6f46 0x3c7ff8e00f80f1d4 0x50f1ffe3803e03c7

def z791 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x33f984998fffffff 0xeccfe612663fffff

def z792 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe4701ffff003f 0xfffff91c07fffc00

def z793 : W := mkw 0xeeee00096f760240 0x23bbb80025bdd809 0xfffe0419ffff0e2f 0xeffff81067fffc38

def z794 : W := mkw 0xeea67b61fa27c4ac 0x37ba99ed87e89f12 0xcc867b61f0070002 0x173219ed87c01c00

def z795 : W := mkw 0xfbb5bed472ac7934 0x17eed6fb51cab1e4 0xf339b80073b87001 0x6bcce6e001cee1c0

def z796 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xf3780001ffff002d 0xefcde00007fffc00

def z797 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc381b8e1f07ff1e9 0x2f0e06e387c1ffc7

def z798 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x33ff84fe0ff8fffd 0xe8cffe13f83fe3ff

def z799 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xffff8001fffff03f 0xeffffe0007ffffc0

def z800 : W := mkw 0x10016f009080ec20 0x104005bc024203b0 0xf001ff01ff80fe37 0xdfc007fc07fe03f8

def z801 : W := mkw 0x0048000805d83b52 0x08012000201760ed 0x333800000ff8ffe1 0x68cce000003fe3ff

def z802 : W := mkw 0xb911a69000000000 0x02e4469a40000000 0xfffffffe0000001f 0xf3fffffff8000000

def z803 : W := mkw 0x044a412b8d5386c9 0x00112904ae354e1b 0x0cc647ff8fff8ffe 0x9c33191ffe3ffe3f

def z804 : W := mkw 0xeeee010b6f760641 0x23bbb8042dbdd819 0xfffe0001ffff0e2f 0xeffff80007fffc38

def z805 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc647ff8c078fd6 0x1433191ffe301e3f

def z806 : W := mkw 0xeaec324c05d83b52 0x0babb0c9301760ed 0xcc867b660ff8ffe2 0x1b3219ed983fe3ff

def z807 : W := mkw 0x044200090c420240 0x0011080024310809 0x0cc647ff8c478ffe 0x9433191ffe311e3f

def z808 : W := mkw 0x43fe90dc257e1352 0x290ffa437095f84d 0x03fe00fe007f01c8 0x200ff803f801fc07

def z809 : W := mkw 0x1111fff49089fdbc 0x144447ffd24227f6 0x0001fffe0000ffd0 0x100007fff80003ff

def z810 : W := mkw 0xbc116f15da80ec20 0x12f045bc576a03b0 0xfc01ff1fff80fe37 0xdff007fc7ffe03f8

def z811 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc381f861f07ff1e3 0x3f0e07e187c1ffc7

def z812 : W := mkw 0x044a492bff7fd7dd 0x24112924affdff5f 0x00000001ffffffe0 0x0c00000007ffffff

def z813 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe0001ffff000e 0x67fff80007fffc00

def z814 : W := mkw 0xac004901da80ec20 0x12b00124076a03b0 0xfc01f801ff80fe37 0xdff007e007fe03f8

def z815 : W := mkw 0xbc016f21da81eca8 0x12f005bc876a07b2 0xfcc7ffffffc7ffff 0xdff31fffffff1fff

def z816 : W := mkw 0x0442012b0c4306c9 0x00110804ac310c1b 0x0cc607fe0c478ffc 0x8033181ff8311e3f

def z817 : W := mkw 0xfaa5260000000000 0x03ea949800000000 0xfffffffe0000001f 0xf3fffffff8000000

def z818 : W := mkw 0xac006b01da80ec20 0x12b001ac076a03b0 0xcc01fb01ff80fe33 0x9f3007ec07fe03f8

def z819 : W := mkw 0xbc7f261d4fd22a42 0x2af1fc98753f48a9 0x3c7e071e0f800e04 0x40f1f81c783e0038

def z820 : W := mkw 0x1059041805d83b52 0x08416410601760ed 0x337804180ff8ffed 0xe8cde010603fe3ff

def z821 : W := mkw 0xeeee32456f760000 0x23bbb8c915bdd800 0xfffe3801ffff002f 0xeffff8e007fffc00

def z822 : W := mkw 0xebb4b2d400000000 0x03aed2cb50000000 0xcffffbfe0000001b 0xb33fffeff8000000

def z823 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x3ffe47ff8c478fff 0xf4fff91ffe311e3f

def z824 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc301b881f07ff1f9 0xaf0c06e207c1ffc7

def z825 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xf001ff01ff80fe31 0x5fc007fc07fe03f8

def z826 : W := mkw 0xb8016e00d280e820 0x12e005b8034a03a0 0xf001fc01ff80fe37 0xdfc007f007fe03f8

def z827 : W := mkw 0xb8012e0052806820 0x12e004b8014a01a0 0xf001bc007f807e05 0x4bc006f001fe01f8

def z828 : W := mkw 0xeeae00016b360000 0x23bab80005acd800 0xfffe0001f3bf000f 0xeffff80007cefc00

def z829 : W := mkw 0xfbb5b6d400081110 0x03eed6db50002044 0xfffffffe0038701f 0xfbfffffff800e1c0

def z830 : W := mkw 0x115b849805da3b52 0x08456e12601768ed 0x33ff84980ffffffd 0xe8cffe12603fffff

def z831 : W := mkw 0xeeae00016b360000 0x23bab80005acd800 0xf3380001f3bf0001 0x6fcce00007cefc00

def z832 : W := mkw 0x43b490d400000000 0x010ed24350000000 0xcffffffe0000001f 0xb33ffffff8000000

def z833 : W := mkw 0x0402412b880386c9 0x00100904ae200e1b 0x0c8647ff8c078ff6 0x9432191ffe301e3f

def z834 : W := mkw 0x43d890d8257c1356 0x0d0f62436095f04d 0x03780098007801c8 0x200de0026001e007

def z835 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xf381f8e1fffff1ff 0xffce07e387ffffc7

def z836 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe0499ffff003f 0xeffff81267fffc00

def z837 : W := mkw 0xbc036f01da82ec20 0x12f00dbc076a0bb0 0xfc87ff01ff87fe37 0xdff21ffc07fe1ff8

def z838 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe40e1ffff003f 0xfffff90387fffc00

def z839 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xf001f801ff80fe33 0xdfc007e007fe03f8

def z840 : W := mkw 0x1159b6dc05d83b52 0x084566db701760ed 0x3ffffffe0ff8ffff 0xf8fffffff83fe3ff

def z841 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe0081ffff81ff 0xeffff80207fffe07

def z842 : W := mkw 0xbc036f03da82ec21 0x12f00dbc0f6a0bb0 0xfc07ff07ff80fe37 0xdff01ffc1ffe03f8

def z843 : W := mkw 0xb8016f00d280ec20 0x12e005bc034a03b0 0xf001ff007f80fe35 0xdbc007fc01fe03f8

def z844 : W := mkw 0xfbb5b6d400802800 0x03eed6db500200a0 0xfffffffe0380701f 0xfbfffffff80e01c0

def z845 : W := mkw 0xeeee10416f760000 0x23bbb84105bdd800 0xfffe7861ffff002f 0xfffff9e187fffc00

def z846 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0xccc647fffc478fff 0x9f33191ffff11e3f

def z847 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc647fe0c478fdc 0x1033191ff8311e3f

def z848 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xffbe0001ffff0023 0x6ffef80007fffc00

def z849 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x337984980fb8ffd5 0x68cde612603ee3ff

def z850 : W := mkw 0x1111849000883910 0x00444612400220e4 0x337984980ff8fffd 0xe8cde612603fe3ff

def z851 : W := mkw 0xbc256f01da80ec20 0x12f095bc076a03b0 0xfc7fff01ff80fe37 0xdff1fffc07fe03f8

def z852 : W := mkw 0xbc016f21da81eca8 0x12f005bc876a07b2 0xfc81ff61ff87fe37 0xdff207fd87fe1ff8

def z853 : W := mkw 0xfbb5b6d442000000 0x03eed6db51080000 0xfffffffe7380001f 0xfbfffffff9ce0000

def z854 : W := mkw 0x14014d01da80ec20 0x10500534076a03b0 0xf001fc01ff80fe37 0xdfc007f007fe03f8

def z855 : W := mkw 0xb835365400000000 0x02e0d4d950000000 0x3c7e7f7e00000004 0x50f1f9fdf8000000

def z856 : W := mkw 0x000048009080e800 0x00000120024203a0 0xc001f801ff80fe33 0x9f0007e007fe03f8

def z857 : W := mkw 0x044a00016f760000 0x2011280005bdd800 0x33380001ffff0021 0x6ccce00007fffc00

def z858 : W := mkw 0xfbbdbed431bc7916 0x0feef6fb50c6f1e4 0xf339b80073b87001 0x6bcce6e001cee1c0

def z859 : W := mkw 0xeaec000025740000 0x03abb0000095d000 0xfffe0001ffff002f 0xeffff80007fffc00

def z860 : W := mkw 0x4380d9e2b02dd59d 0x050e03678ac0b756 0xc381fbe7f07ff1fb 0xbf0e07ef9fc1ffc7

def z861 : W := mkw 0xeeee22056f760000 0x23bbb88815bdd800 0xfffe0307ffff002f 0xeffff80c1ffffc00

def z862 : W := mkw 0x46ca00016f760000 0x211b280005bdd800 0xf3f80001ffff002f 0xefcfe00007fffc00

def z863 : W := mkw 0x42804820b02dd19c 0x050a012082c0b746 0xc381f801f07ff1fb 0xbf0e07e007c1ffc7

def z864 : W := mkw 0x044a412b8d5386c9 0x00112904ae354e1b 0x3cfe47ff8fc78ffe 0xd4f3f91ffe3f1e3f

def z865 : W := mkw 0xb8012e0052806820 0x12e004b8014a01a0 0xf001b8007f80fe21 0x4bc006e001fe03f8

def z866 : W := mkw 0x044a412bcf5386c9 0x20112904af3d4e1b 0x0cc647ff8fc78ffe 0x9433191ffe3f1e3f

def z867 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc41ff99ff80fe3f 0xdff107fe67fe03f8

def z868 : W := mkw 0xbc014c01da80e800 0x02f00530076a03a0 0xfc01fc01ff80fe37 0xdff007f007fe03f8

def z869 : W := mkw 0x1111b6d400000000 0x004446db50000000 0x3ffffffe0000001f 0xf0fffffff8000000

def z870 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc381fffff07ff1fb 0xbf0e07ffffc1ffc7

def z871 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfffffffff000003f 0xffffffffffc00000

def z872 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xcf87fbe7f07ff1fb 0xbf3e1fef9fc1ffc7

def z873 : W := mkw 0x044a492bdfdbfffb 0x18112924af7f6fff 0x00000001ffffffe0 0x0c00000007ffffff

def z874 : W := mkw 0xbc0126014a802800 0x02f00498052a00a0 0xfc01ff01ff80fe37 0xdff007fc07fe03f8

def z875 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xf001bc01ff80fe35 0xcfc006f007fe03f8

def z876 : W := mkw 0xbc012f015a806c20 0x12f004bc056a01b0 0xfc01ff007f807e17 0xdbf007fc01fe01f8

def z877 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x333984000ff8fff5 0xe8cce610003fe3ff

def z878 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfffffffe0000f03f 0xfbfffffff80003c0

def z879 : W := mkw 0x0442492bde43c6e9 0x10110924af790f1b 0x0cc647fffc478ffe 0x9433191ffff11e3f

def z880 : W := mkw 0x1049040805d83b52 0x08412410201760ed 0x337984000ff8fffd 0xe8cde610003fe3ff

def z881 : W := mkw 0x0158809805d83b52 0x08056202601760ed 0x337800980ff8ffed 0xe8cde002603fe3ff

def z882 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01ff81ffc0ffff 0xdff007fe07ff03ff

def z883 : W := mkw 0xeeee00096f760240 0x23bbb80025bdd809 0xfffe47ffffff8fff 0xfffff91ffffffe3f

def z884 : W := mkw 0x1159a69c05d83b52 0x0845669a701760ed 0x3379879e0ff8fffd 0xe8cde61e783fe3ff

def z885 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe0401ffff8e3f 0xeffff81007fffe38

def z886 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xf3b80001ffff002b 0xefcee00007fffc00

def z887 : W := mkw 0xb835261400000000 0x02e0d49850000000 0xfcfffffe0000001f 0xd3f3fffff8000000

def z888 : W := mkw 0x1111ccb89089fbde 0x0c444732e24227ef 0x000184980000ffd0 0x00000612600003ff

def z889 : W := mkw 0x1159a69805d83b52 0x0845669a601760ed 0x3379ff980ff8fffd 0xf8cde7fe603fe3ff

def z890 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe4367ffff002f 0xfffff90d9ffffc00

def z891 : W := mkw 0xac004901da00c400 0x02b0012407680310 0xfc01ff01ff80fe37 0xdff007fc07fe03f8

def z892 : W := mkw 0x0048000805d83b52 0x08012000201760ed 0x337804980ff8fffd 0xe8cde012603fe3ff

def z893 : W := mkw 0xeec800016f740000 0x03bb200005bdd000 0xfff80001ffff002f 0xefffe00007fffc00

def z894 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x337984980ff8ffdc 0x60cde612603fe3ff

def z895 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfffffbfe0000000b 0x73ffffeff8000000

def z896 : W := mkw 0xfbb5b6d462240000 0x23eed6db51889000 0xfffffffe7000001f 0xf3fffffff9c00000

def z897 : W := mkw 0x1049040805d02a40 0x00412410201740a9 0x337984980ff8fffd 0xe8cde612603fe3ff

def z898 : W := mkw 0x115994dc05d83b52 0x08456653701760ed 0x337984fe0ff8fffd 0xe8cde613f83fe3ff

def z899 : W := mkw 0x43da90fa257f13df 0x0d0f6a43e895fc4f 0x03fe00fe007f01c8 0x200ff803f801fc07

def z900 : W := mkw 0x00004820b02dd19c 0x0400012082c0b746 0xc001b801f07ff1e1 0x0f0006e007c1ffc7

def z901 : W := mkw 0xb935b6d400000000 0x02e4d6db50000000 0x3f7ffffe0000001d 0xf0fdfffff8000000

def z902 : W := mkw 0x115994d805d83b52 0x08456653601760ed 0x3379fcf80ff8fffd 0xf8cde7f3e03fe3ff

def z903 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe0001f3ff000b 0x6ffff80007cffc00

def z904 : W := mkw 0xbc036f23da83eca9 0x12f00dbc8f6a0fb2 0xfc01ff01ff87fe37 0xdff007fc07fe1ff8

def z905 : W := mkw 0xb8012e0052806820 0x12e004b8014a01a0 0xfc01ff007f80fe37 0xdbf007fc01fe03f8

def z906 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x3f79c7980ff8ffff 0xf8fde71e603fe3ff

def z907 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfffe7ffe0000000e 0x73fff9fff8000000

def z908 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xff01ff01fff8fe3f 0xfffc07fc07ffe3f8

def z909 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfffffffe0078003f 0xfbfffffff801e000

def z910 : W := mkw 0x1111dcf09089f99e 0x0c444773c24227e6 0x0001f8e00000f1d0 0x100007e3800003c7

def z911 : W := mkw 0xeeee32456f760000 0x23bbb8c915bdd800 0xfffe7fffffff003f 0xfffff9fffffffc00

def z912 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xffffffff8047003f 0xf7fffffffe011c00

def z913 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x3fff84980ff8ffff 0xe8fffe12603fe3ff

def z914 : W := mkw 0xfbb5b6d400802800 0x03eed6db500200a0 0xfffffffe0000fe1f 0xf3fffffff80003f8

def z915 : W := mkw 0x044a412b8d5386c9 0x00112904ae354e1b 0x0ffe47ff8c7f8ffe 0xb43ff91ffe31fe3f

def z916 : W := mkw 0xfab5365400000000 0x03ead4d950000000 0xfcfe7ffe0000001e 0xd3f3f9fff8000000

def z917 : W := mkw 0xbc276f01da82ec20 0x32f09dbc076a0bb0 0xfc07ff01ff80fe37 0xdff01ffc07fe03f8

def z918 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x33f9c4f80ff8ffff 0xf8cfe713e03fe3ff

def z919 : W := mkw 0xeeee010b6f760641 0x23bbb8042dbdd819 0xfffe079fffff8fff 0xeffff81e7ffffe3f

def z920 : W := mkw 0x43a4d8e4b02dd19c 0x050e936392c0b746 0xc387f8e7f07ff1fb 0xbf0e1fe39fc1ffc7

def z921 : W := mkw 0x0042412a844386c9 0x00010904aa110e1b 0x0cc647fe00478fde 0x9033191ff8011e3f

def z922 : W := mkw 0x0442492b9c43c6c9 0x00110924ae710f1b 0xccc67ffffc478ffe 0x973319fffff11e3f

def z923 : W := mkw 0x0042002a044302c9 0x00010800a8110c0b 0x0cc647fe0c478ffe 0x9033191ff8311e3f

def z924 : W := mkw 0xbc5b271b4fd22e63 0x1af16c9c6d3f48b9 0x3c7e071e0f800e04 0x40f1f81c783e0038

def z925 : W := mkw 0xeeee01036f760401 0x23bbb8040dbdd810 0xfffe0307ffff002f 0xeffff80c1ffffc00

def z926 : W := mkw 0x43c890e8257d13de 0x0d0f2243a095f44f 0x038000e0007f01c8 0x200e00038001fc07

def z927 : W := mkw 0xeeee01016f760400 0x23bbb80405bdd810 0xfffe0701ffff0e2f 0xeffff81c07fffc38

def z928 : W := mkw 0x10010c0010806800 0x00400430004201a0 0xf001bc007f80fe35 0xcbc006f001fe03f8

def z929 : W := mkw 0xbc036f23da83eca9 0x12f00dbc8f6a0fb2 0xfcc7ffffff87fe3f 0xdff31ffffffe1ff8

def z930 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xf3fe0001ffff0029 0x6fcff80007fffc00

def z931 : W := mkw 0xebb4b2d400000000 0x03aed2cb50000000 0xfffe7bfe0000000f 0xf3fff9eff8000000

def z932 : W := mkw 0xac4a00016f760000 0x22b1280005bdd800 0xff780001ffff002f 0xeffde00007fffc00

def z933 : W := mkw 0x43a4d8e0b02dd19c 0x050e936382c0b746 0xc3fff8e1f07ff1fb 0xbf0fffe387c1ffc7

def z934 : W := mkw 0xbc012e015a806820 0x12f004b8056a01a0 0xfc01bc01ff80fe37 0xcff006f007fe03f8

def z935 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc647ff80478fda 0x1433191ffe011e3f

def z936 : W := mkw 0x438098e0302d519c 0x050e026380c0b546 0xc381b8e1f07f71eb 0xaf0e06e387c1fdc7

def z937 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc301f8e1f07ff1f1 0x3f0c07e387c1ffc7

def z938 : W := mkw 0xfbb5b6d400883910 0x03eed6db500220e4 0xfffffffe0ff8ffff 0xfbfffffff83fe3ff

def z939 : W := mkw 0xeea65963fa27c48d 0x27ba99658fe89f12 0xcc867b67f0070002 0x173219ed9fc01c00

def z940 : W := mkw 0xfbb5b6d4202c1114 0x07eed6db5080b044 0xfffffffe0038001f 0xf3fffffff800e000

def z941 : W := mkw 0x4380c880b02cd110 0x010e032202c0b344 0xc381f881f07ff1fb 0xbf0e07e207c1ffc7

def z942 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0c8647ff8c478ff2 0x1432191ffe311e3f

def z943 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xcc01ff01ff80fe32 0x1f3007fc07fe03f8

def z944 : W := mkw 0x0442492b9c43c6c9 0x00110924ae710f1b 0x0cc647fffc47fffe 0x9c33191ffff11fff

def z945 : W := mkw 0xeaec000067740000 0x23abb000019dd000 0xf3f80001ffff002f 0xefcfe00007fffc00

def z946 : W := mkw 0x04004901da80ec20 0x10100124076a03b0 0xc001b801ff80fe21 0x0f0006e007fe03f8

def z947 : W := mkw 0x43b4d8f4b02dd19c 0x050ed363d2c0b746 0xc3b9f8e1f07ff1fb 0xbf0ee7e387c1ffc7

def z948 : W := mkw 0xbc036f23da83eca9 0x12f00dbc8f6a0fb2 0xfc87ffe7ffc7ffff 0xdff21fff9fff1fff

def z949 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xcffffffe0000001a 0x333ffffff8000000

def z950 : W := mkw 0x53b5b6d400000000 0x014ed6db50000000 0x0ffffffe0000001e 0xb03ffffff8000000

def z951 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc381f8e1f07ff1da 0x370e07e387c1ffc7

def z952 : W := mkw 0xbc356f15da80ec20 0x12f0d5bc576a03b0 0xfcffffffff80fe3f 0xdff3fffffffe03f8

def z953 : W := mkw 0xfbb5b6d420240000 0x03eed6db50809000 0xfffffffe007f001f 0xf3fffffff801fc00

def z954 : W := mkw 0xbc012f015a806c20 0x12f004bc056a01b0 0xfc01bf007f80fe35 0xcbf006fc01fe03f8

def z955 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc381fce1fc7fffff 0xbf0e07f387f1ffff

def z956 : W := mkw 0x0100c8a09009d198 0x0004032282402746 0xc381f8e1f07ff1fb 0xbf0e07e387c1ffc7

def z957 : W := mkw 0x43fe90f8257f13de 0x2d0ffa43e095fc4f 0x03fe00f8007f01c8 0x200ff803e001fc07

def z958 : W := mkw 0x044a492bfff7eee9 0x30112924afffdfbb 0x00000001ffffffe0 0x0c00000007ffffff

def z959 : W := mkw 0x0400412188018488 0x0010010486200612 0x0cc647ff8c478ffe 0x9433191ffe311e3f

def z960 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x337980980ff8ffe9 0x68cde602603fe3ff

def z961 : W := mkw 0x14016f01da80ec20 0x105005bc076a03b0 0xc001ff01ff80fe33 0x9f0007fc07fe03f8

def z962 : W := mkw 0xbc116f11da80ec20 0x12f045bc476a03b0 0xfc79ff19ff80fe37 0xdff1e7fc67fe03f8

def z963 : W := mkw 0xac6e00016f760000 0x22b1b80005bdd800 0x3f7e0001ffff002d 0xecfdf80007fffc00

def z964 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xff79ff01ff80fe3f 0xfffde7fc07fe03f8

def z965 : W := mkw 0xeeee00096f760240 0x23bbb80025bdd809 0xfffe0001ffff8fef 0xeffff80007fffe3f

def z966 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x3f7f879e0ff8fffd 0xe8fdfe1e783fe3ff

def z967 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xcf81ffe1f07ff1ff 0xbf3e07ff87c1ffc7

def z968 : W := mkw 0x1111ddfa9089ffdf 0x0c444777ea4227ff 0x0001fffe0000ffd0 0x100007fff80003ff

def z969 : W := mkw 0xeaa4324400000000 0x03aa90c910000000 0xfffe7ffe0000001f 0xf3fff9fff8000000

def z970 : W := mkw 0xbc016f21da81eca8 0x12f005bc876a07b2 0xfc01ff01ffc7fff7 0xdff007fc07ff1fff

def z971 : W := mkw 0x1159b6dc05d83b52 0x084566db701760ed 0x3379bc980ff8fffd 0xe8cde6f2603fe3ff

def z972 : W := mkw 0x42805860b02dd19c 0x050a016182c0b746 0xc081f861f07ff1f3 0x9f0207e187c1ffc7

def z973 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01ff007f80fe15 0x5bf007fc01fe03f8

def z974 : W := mkw 0x00004820b02dd19c 0x0400012082c0b746 0xc081f8e1f07ff1fb 0x9f0207e387c1ffc7

def z975 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x3379c7fe0ff8fffd 0xf8cde71ff83fe3ff

def z976 : W := mkw 0xeaac000063340000 0x23aab000018cd000 0xf3b80001f3bf0003 0x6fcee00007cefc00

def z977 : W := mkw 0xbc7f27194fd22e62 0x3af1fc9c653f48b9 0x3c7e07180f800e04 0x40f1f81c603e0038

def z978 : W := mkw 0x0442012b0c4306c9 0x00110804ac310c1b 0x0cc607ff8c470fee 0x8433181ffe311c3f

def z979 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc87ff67ff80fe37 0xdff21ffd9ffe03f8

def z980 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01b801ff80fe27 0xcff006e007fe03f8

def z981 : W := mkw 0xbc016f21da81eca8 0x12f005bc876a07b2 0xfc01ffe1ff80fff7 0xdff007ff87fe03ff

def z982 : W := mkw 0x43ee90ea257f13dd 0x250fba43a895fc4f 0x03fe00fe007f01c8 0x200ff803f801fc07

def z983 : W := mkw 0x0100c8a0b02dd19c 0x0404032282c0b746 0xc301f881f07ff1fb 0xbf0c07e207c1ffc7

def z984 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0xf379fc980ff8ffff 0xfbcde7f2603fe3ff

def z985 : W := mkw 0xeea66b23fa27c4a9 0x33ba99ac8fe89f12 0xcc867b67f0070002 0x173219ed9fc01c00

def z986 : W := mkw 0xeeee10456f760000 0x23bbb84115bdd800 0xfffe0067ffff002f 0xeffff8019ffffc00

def z987 : W := mkw 0x43b4d8f4b02dd19c 0x050ed363d2c0b746 0xcffffffff07ff1ff 0xbf3fffffffc1ffc7

def z988 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfcfffffe00000016 0x53f3fffff8000000

def z989 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc3c1fcf9f07ff1ff 0xbf0f07f3e7c1ffc7

def z990 : W := mkw 0x1111fff89089fffe 0x1c4447ffe24227ff 0x0001fff80000ffd0 0x100007ffe00003ff

def z991 : W := mkw 0xfbb5b6d4202c1110 0x03eed6db5080b044 0xfffffffff07ff1ff 0xffffffffffc1ffc7

def z992 : W := mkw 0xbc6f270b4fd22e61 0x32f1bc9c2d3f48b9 0x3c7e071e0f800e04 0x40f1f81c783e0038

def z993 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xcfc7f8e1f07ff1ff 0xbf3f1fe387c1ffc7

def z994 : W := mkw 0xfbb5b6d400081110 0x03eed6db50002044 0xfffffffe0000f1df 0xf3fffffff80003c7

def z995 : W := mkw 0xfbb5b6d400000000 0x03eed6db50000000 0xfffffffe0f80003f 0xfbfffffff83e0000

def z996 : W := mkw 0x04004901da80ec20 0x10100124076a03b0 0xcc01ff01ff80fe37 0x9f3007fc07fe03f8

def z997 : W := mkw 0x0442412b8c4386c9 0x00110904ae310e1b 0x0cc647ff8c470fce 0x1433191ffe311c3f

def z998 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc381f8e1f07f71cb 0x3f0e07e387c1fdc7

def z999 : W := mkw 0x4288000021340000 0x010a20000084d000 0xf3b80001f3ff002b 0xefcee00007cffc00

def z1000 : W := mkw 0x1111fefc9089fbde 0x0c4447fbf24227ef 0x0001fffe0000ffd0 0x100007fff80003ff

def z1001 : W := mkw 0x0402412b880386c9 0x00100904ae200e1b 0x0cc647ff80078fde 0x9433191ffe001e3f

def z1002 : W := mkw 0x438090c0202c1110 0x010e02430080b044 0xc381f8e1f07ff1fb 0xbf0e07e387c1ffc7

def z1003 : W := mkw 0xeeae00016b360000 0x23bab80005acd800 0xffbe0001f3ff002b 0xeffef80007cffc00

def z1004 : W := mkw 0x044a00016f760000 0x2011280005bdd800 0x3ffe0001ffff002f 0xecfff80007fffc00

def z1005 : W := mkw 0xbc016f01da80ec20 0x12f005bc076a03b0 0xfc01ff01ff80fe16 0x57f007fc07fe03f8

def z1006 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0xfffe0001ffbf0007 0x6ffff80007fefc00

def z1007 : W := mkw 0x4380d8e0b02dd19c 0x050e036382c0b746 0xc301f801f07ff1f3 0xbf0c07e007c1ffc7

def z1008 : W := mkw 0x044a492bbdffffdf 0x0c112924aef7ffff 0x00000001ffffffe0 0x0c00000007ffffff

def z1009 : W := mkw 0xfbb5b6d400081110 0x03eed6db50002044 0xfffffffe007801df 0xf3fffffff801e007

def z1010 : W := mkw 0xeeee00016f760000 0x23bbb80005bdd800 0x3ffe0001ffff002c 0x6cfff80007fffc00

def z1011 : W := mkw 0xbc016f23da81eca9 0x12f005bc8f6a07b2 0xfc01ff67ff80fe37 0xdff007fd9ffe03f8

def z1012 : W := mkw 0xfab5365400000000 0x03ead4d950000000 0xfffe7f7e0000000f 0xf3fff9fdf8000000

def z1013 : W := mkw 0xfbb5b6d400802800 0x03eed6db500200a0 0xfffffffe0f800e1f 0xf3fffffff83e0038

def z1014 : W := mkw 0xbc012f015a806c20 0x12f004bc056a01b0 0xfc01bf01ff807e27 0xcff006fc07fe01f8

def z1015 : W := mkw 0xbc012f015a806c20 0x12f004bc056a01b0 0xf001b8007f807e01 0x4bc006e001fe01f8

def z1016 : W := mkw 0x0100d8e0b02dd19c 0x0404036382c0b746 0xc001f8e1f07ff1f3 0x9f0007e387c1ffc7

def z1017 : W := mkw 0x46ca00012d760000 0x011b280004b5d800 0xfffe0001ffff002f 0xeffff80007fffc00

def z1018 : W := mkw 0x0442012b0c4306c9 0x00110804ac310c1b 0x0cc647fe0c470fde 0x9033191ff8311c3f

def z1019 : W := mkw 0xeab4325400000000 0x03aad0c950000000 0xccfe7b7e00000002 0x1333f9edf8000000

def z1020 : W := mkw 0xeeee23016f760420 0x33bbb88c05bdd810 0xfffe0301ffff002f 0xeffff80c07fffc00

def z1021 : W := mkw 0xac4a00014f520000 0x02b12800053d4800 0xfffe0001ffff002f 0xeffff80007fffc00

def z1022 : W := mkw 0xfbb5b6d400883912 0x0beed6db500220e4 0xfffffffe0000701f 0xf3fffffff80001c0

def z1023 : W := mkw 0x438098c0302c5114 0x050e026300c0b144 0xc381b881f07ff1fb 0xaf0e06e207c1ffc7

def z1024 : W := mkw 0xeeac00016b340000 0x23bab00005acd000 0xffb80001ffff002f 0xeffee00007fffc00

def z1025 : W := mkw 0x42804820b025c088 0x010a012082c09702 0xc381f8e1f07ff1fb 0xbf0e07e387c1ffc7

def z1026 : W := mkw 0x00404028844182c8 0x00010100a211060b 0x0cc647ff8c478ffe 0x9433191ffe311e3f

def z1027 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0xf3798499fff8ffff 0xefcde61267ffe3ff

def z1028 : W := mkw 0xebb4b2d400000000 0x03aed2cb50000000 0xcffe7ffe0000001e 0xb33ff9fff8000000

def z1029 : W := mkw 0x1159849805d83b52 0x08456612601760ed 0x337984180ff8ffe5 0x68cde610603fe3ff

def z1030 : W := mkw 0xbc256f05da80ec20 0x12f095bc176a03b0 0xfc07ff07ff80fe37 0xdff01ffc1ffe03f8

def z1031 : W := mkw 0x4380d9e0b02dd59c 0x050e036782c0b756 0xc381ffe1f07ffffb 0xbf0e07ff87c1ffff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z8,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z9]),(0,[z0,z1,z3,z10,z4,z5,z6]),(0,[z0,z1,z3,z4,z11,z5,z6]),(0,[z12,z0,z1,z3,z4,z5,z6]),(0,[z13,z0,z1,z3,z4,z5,z14])],[(0,[z15,z0,z1,z3,z4,z5,z6]),(0,[z0,z16,z1,z3,z4,z5,z6]),(0,[z17,z1,z3,z4,z5,z18,z6]),(0,[z0,z1,z3,z4,z19,z5,z6]),(0,[z20,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z21,z5,z6,z22])],[(1,[z0,z1,z3,z4,z23,z6]),(0,[z0,z24,z1,z3,z4,z5,z25])],[(0,[z0,z1,z3,z26,z5,z6,z22]),(0,[z27,z0,z1,z3,z4,z5,z28]),(0,[z29,z0,z30,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z31]),(0,[z0,z1,z3,z4,z5,z32,z6])],[],[(0,[z0,z33,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z34,z6]),(0,[z0,z1,z3,z4,z5,z6,z35]),(0,[z0,z36,z1,z3,z4,z6,z37])],[(0,[z38,z1,z3,z4,z5,z18,z6]),(0,[z39,z0,z1,z3,z4,z5,z6]),(0,[z40,z0,z1,z3,z4,z5,z6]),(0,[z0,z41,z1,z3,z4,z5,z6]),(0,[z42,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z43,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z44]),(0,[z0,z1,z3,z4,z45,z5,z6])],[(0,[z0,z46,z1,z3,z4,z5,z6]),(0,[z29,z0,z1,z47,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z48])],[(0,[z49,z0,z1,z3,z4,z5,z6]),(0,[z0,z50,z3,z47,z4,z5,z6]),(0,[z0,z1,z51,z3,z4,z5,z6]),(0,[z52,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z53,z5,z6]),(0,[z0,z1,z54,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z5,z6])],[(0,[z0,z1,z3,z56,z4,z5,z6]),(0,[z0,z1,z3,z57,z4,z5,z6]),(0,[z58,z0,z59,z3,z4,z5,z6]),(0,[z0,z60,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z61,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z25]),(0,[z0,z1,z3,z4,z5,z6,z62])],[(0,[z63,z1,z3,z64,z4,z5,z6]),(0,[z0,z60,z1,z3,z4,z65,z6]),(0,[z66,z0,z1,z3,z4,z5,z6]),(0,[z67,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z68,z6])],[(0,[z0,z1,z69,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z70]),(0,[z0,z71,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z72,z6]),(0,[z0,z1,z3,z73,z4,z74,z5]),(1,[z0,z1,z75,z4,z76,z6]),(0,[z0,z1,z3,z4,z77,z5,z6]),(0,[z0,z1,z78,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z79]),(0,[z0,z1,z50,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z80,z5,z6]),(0,[z0,z1,z3,z4,z81,z5,z6]),(0,[z82,z0,z1,z3,z4,z5,z6]),(0,[z0,z83,z1,z3,z4,z5,z6])]],
   [[(0,[z84,z0,z1,z3,z4,z5,z6]),(0,[z0,z60,z1,z75,z3,z4,z6]),(0,[z0,z1,z3,z85,z4,z5,z6]),(0,[z0,z86,z1,z3,z4,z5,z6])],[],[(0,[z87,z0,z88,z1,z3,z4,z6]),(0,[z13,z0,z1,z89,z4,z5,z6])],[(0,[z0,z1,z3,z4,z90,z5,z6]),(0,[z7,z0,z8,z3,z4,z5,z6]),(0,[z91,z0,z1,z3,z4,z5,z6]),(0,[z92,z1,z3,z4,z26,z5,z6]),(0,[z0,z1,z3,z47,z4,z5,z6]),(0,[z0,z88,z60,z1,z3,z4,z6]),(0,[z0,z1,z3,z93,z4,z5,z6])],[(0,[z94,z0,z1,z3,z4,z5,z6]),(0,[z95,z0,z1,z3,z4,z5,z6]),(0,[z0,z96,z1,z97,z3,z4,z6])],[(0,[z98,z0,z1,z3,z4,z5,z6]),(0,[z0,z99,z1,z3,z4,z5,z6]),(0,[z0,z1,z100,z3,z4,z5,z6]),(0,[z87,z0,z1,z3,z4,z6,z101]),(0,[z102,z0,z1,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z6,z103]),(0,[z104,z0,z1,z105,z3,z5,z6]),(0,[z0,z1,z89,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z106,z5,z6])],[(0,[z0,z1,z3,z107,z4,z5,z6]),(0,[z0,z88,z36,z1,z3,z4,z6])],[(0,[z38,z0,z1,z3,z108,z5,z6]),(0,[z0,z1,z109,z3,z4,z5,z6]),(0,[z110,z0,z1,z3,z4,z5,z6]),(0,[z0,z111,z1,z3,z4,z5,z6]),(1,[z112,z0,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z113]),(0,[z1,z3,z4,z114,z5,z18,z6]),(0,[z0,z1,z3,z89,z4,z5,z6]),(0,[z112,z0,z36,z3,z4,z5,z6])],[(1,[z0,z1,z3,z115,z5,z6]),(0,[z116,z0,z1,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z5,z18,z6]),(0,[z117,z0,z1,z3,z4,z5,z6]),(0,[z27,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z105,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z118,z6]),(0,[z0,z1,z3,z26,z5,z6,z119]),(0,[z87,z120,z1,z3,z4,z5,z6]),(1,[z102,z0,z1,z5,z6,z119])],[(0,[z0,z1,z121,z3,z4,z5,z6])],[(0,[z122,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z123,z5,z6]),(0,[z0,z1,z3,z124,z4,z5,z6]),(0,[z102,z125,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z126]),(0,[z0,z127,z1,z3,z4,z5,z6]),(0,[z0,z96,z1,z3,z4,z6,z128])],[(0,[z0,z129,z1,z3,z4,z5,z6]),(0,[z130,z0,z1,z3,z73,z5,z6])]],
   [[(0,[z0,z8,z3,z4,z5,z6,z25]),(0,[z0,z1,z3,z4,z5,z131,z6]),(0,[z0,z59,z1,z3,z4,z5,z132])],[(0,[z17,z0,z1,z3,z4,z5,z6]),(0,[z133,z0,z1,z3,z4,z5,z6]),(0,[z27,z0,z134,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z135,z5,z6]),(0,[z102,z0,z1,z3,z4,z5,z6]),(0,[z136,z0,z1,z75,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z137]),(0,[z138,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z139,z6]),(0,[z0,z1,z3,z4,z65,z18,z6]),(0,[z140,z0,z1,z3,z4,z5,z6]),(0,[z0,z141,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z142]),(0,[z0,z88,z1,z3,z4,z5,z37])],[(0,[z27,z0,z1,z3,z80,z5,z6]),(0,[z0,z1,z3,z4,z5,z28,z6])],[(0,[z0,z30,z1,z50,z4,z5,z6]),(0,[z0,z1,z75,z4,z5,z76,z6]),(0,[z0,z143,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z144,z4,z5,z6]),(0,[z0,z125,z1,z3,z4,z5,z6]),(0,[z145,z0,z1,z3,z4,z5,z6])],[(0,[z58,z0,z1,z3,z146,z5,z6])],[(0,[z1,z147,z3,z64,z4,z5,z6]),(0,[z0,z1,z3,z148,z4,z74,z5]),(0,[z0,z1,z3,z4,z5,z6,z149]),(0,[z13,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z150,z3,z4,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6])],[(0,[z151,z0,z1,z3,z4,z5,z6]),(0,[z0,z152,z1,z3,z4,z5,z6]),(0,[z0,z1,z153,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z154]),(0,[z0,z1,z3,z4,z5,z155,z6]),(0,[z0,z1,z3,z4,z5,z156,z6]),(0,[z157,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z158,z4,z5,z6]),(0,[z159,z0,z1,z3,z4,z5,z6])],[(0,[z160,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z75,z3,z85,z4,z5])],[(0,[z161,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z162,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z163]),(0,[z0,z1,z3,z4,z164,z5,z6])],[(0,[z165,z0,z1,z3,z4,z5,z6]),(0,[z166,z0,z1,z3,z4,z5,z6]),(0,[z0,z167,z1,z3,z4,z5,z6]),(0,[z27,z0,z1,z168,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z169]),(0,[z0,z1,z170,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z171]),(0,[z172,z0,z1,z3,z4,z5,z6])],[(0,[z102,z58,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z173,z4,z5,z6]),(0,[z0,z1,z174,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z175]),(0,[z27,z176,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z177,z4,z5,z6]),(0,[z0,z1,z178,z4,z5,z6,z14])],[(0,[z0,z1,z3,z179,z4,z5,z6]),(1,[z0,z1,z3,z4,z180,z37])],[(0,[z181,z0,z1,z3,z4,z5,z6]),(0,[z66,z0,z182,z3,z4,z5,z6]),(0,[z0,z1,z183,z3,z4,z5,z6]),(0,[z0,z1,z3,z184,z4,z5,z6]),(0,[z0,z96,z1,z97,z3,z5,z6]),(0,[z0,z1,z3,z185,z4,z5,z6])],[(1,[z0,z1,z3,z108,z5,z6]),(0,[z0,z1,z3,z4,z18,z6,z37]),(0,[z186,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z187]),(0,[z0,z1,z3,z188,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z189,z6]),(0,[z0,z1,z3,z4,z190,z5,z6])],[(1,[z0,z191,z1,z3,z4,z6]),(0,[z192,z0,z1,z3,z4,z5,z6])],[(0,[z0,z193,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z194]),(0,[z195,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z196])],[(0,[z0,z1,z3,z4,z5,z6,z197]),(0,[z198,z0,z1,z3,z4,z5,z6])],[]],
   [[(0,[z0,z1,z3,z4,z199,z5,z6]),(0,[z200,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z64,z4,z5,z6]),(0,[z201,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z202,z3,z4,z5,z6]),(0,[z0,z3,z4,z65,z5,z6,z101]),(0,[z0,z1,z3,z4,z203,z5,z6]),(0,[z204,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z73,z4,z5,z6])],[(0,[z0,z1,z3,z4,z65,z5,z6]),(0,[z0,z1,z3,z205,z4,z5,z6]),(0,[z0,z1,z206,z3,z4,z5,z6])],[(0,[z0,z60,z1,z3,z4,z6,z37]),(0,[z0,z207,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z208,z4,z5,z6]),(1,[z0,z1,z3,z57,z5,z6]),(0,[z0,z1,z178,z3,z4,z5,z6]),(0,[z209,z0,z1,z3,z4,z5,z6]),(0,[z0,z210,z1,z3,z4,z5,z6]),(0,[z211,z0,z1,z3,z4,z5,z6])],[(0,[z136,z0,z1,z3,z4,z18,z6]),(0,[z176,z0,z1,z3,z4,z5,z212]),(0,[z213,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z214,z4,z5,z6]),(0,[z0,z1,z3,z148,z21,z4,z5])],[(1,[z0,z1,z3,z85,z4,z5])],[(1,[z120,z1,z3,z4,z5,z6]),(0,[z66,z0,z3,z4,z74,z5,z6]),(0,[z0,z215,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z216,z5,z6]),(0,[z217,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z218,z6]),(0,[z0,z1,z3,z4,z5,z6,z31]),(0,[z0,z219,z1,z3,z4,z5,z6])],[(0,[z0,z1,z220,z3,z4,z5,z6]),(0,[z221,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z222]),(1,[z223,z1,z3,z4,z114,z6])],[(0,[z0,z1,z147,z3,z4,z5,z6]),(0,[z224,z0,z1,z3,z4,z5,z6]),(0,[z0,z59,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z225]),(0,[z0,z226,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z212]),(0,[z102,z0,z1,z3,z5,z6,z22]),(0,[z227,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z228]),(0,[z0,z1,z229,z3,z4,z5,z6]),(0,[z0,z1,z3,z230,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z231]),(0,[z0,z232,z1,z3,z4,z5,z6]),(0,[z0,z233,z1,z3,z4,z74,z6])],[(0,[z234,z0,z1,z3,z4,z5,z6]),(1,[z0,z96,z1,z97,z3,z6]),(0,[z104,z0,z1,z3,z148,z5,z6]),(0,[z0,z1,z3,z235,z4,z5,z6])],[(0,[z0,z1,z3,z236,z5,z6,z128])]],
   [[(0,[z223,z1,z8,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z237,z6]),(0,[z238,z0,z1,z3,z4,z5,z6]),(0,[z0,z239,z1,z3,z4,z5,z6]),(0,[z0,z1,z105,z89,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z240])],[(0,[z0,z1,z3,z4,z5,z241,z6]),(1,[z0,z1,z3,z242,z5,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z243,z0,z1,z3,z4,z5,z6])],[(0,[z244,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z245,z5,z6]),(0,[z0,z1,z3,z246,z4,z5,z6]),(1,[z0,z60,z3,z4,z65,z6]),(0,[z0,z24,z1,z3,z4,z74,z5]),(0,[z0,z1,z3,z247,z4,z5,z6]),(0,[z0,z1,z3,z4,z248,z5,z6])],[(0,[z63,z0,z1,z64,z4,z5,z6]),(0,[z249,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z250]),(0,[z92,z0,z1,z3,z251,z5,z6])],[(0,[z0,z1,z252,z3,z4,z5,z6]),(0,[z17,z0,z1,z3,z4,z18,z6]),(0,[z0,z30,z1,z47,z4,z5,z6]),(0,[z0,z253,z1,z3,z4,z5,z6]),(0,[z0,z96,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z254,z6])],[(0,[z104,z0,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z255,z5,z6]),(0,[z0,z1,z3,z256,z4,z5,z6])],[(0,[z257,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z258,z5,z6])],[(0,[z0,z1,z178,z3,z73,z4,z5]),(0,[z0,z1,z259,z3,z4,z5,z6])]],
   [[(0,[z0,z260,z1,z3,z4,z5,z6]),(0,[z0,z59,z1,z3,z246,z5,z6]),(1,[z0,z1,z3,z4,z261,z5]),(0,[z0,z88,z36,z1,z3,z4,z5])],[(1,[z38,z182,z3,z4,z5,z6]),(0,[z262,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z263,z5,z6]),(0,[z0,z1,z3,z264,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z37])],[(1,[z92,z1,z3,z26,z5,z6]),(0,[z265,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z105,z3,z5,z6,z119]),(0,[z0,z1,z3,z266,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z267,z6]),(0,[z0,z1,z268,z3,z4,z5,z6]),(0,[z0,z1,z3,z148,z4,z5,z6])],[(0,[z269,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z270]),(0,[z271,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z272,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z273,z6])],[(0,[z274,z0,z1,z3,z4,z5,z6]),(0,[z136,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z275,z4,z5,z6]),(0,[z0,z276,z1,z3,z4,z5,z6]),(0,[z277,z1,z3,z4,z26,z5,z6]),(0,[z87,z0,z3,z4,z5,z6,z25]),(0,[z66,z0,z1,z3,z4,z5,z25]),(0,[z0,z1,z3,z4,z5,z278,z6]),(0,[z279,z0,z1,z3,z4,z5,z6])],[(0,[z280,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z281,z5,z6]),(0,[z282,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z283])]],
   [[(0,[z0,z284,z1,z3,z4,z5,z6]),(0,[z27,z0,z1,z285,z4,z5,z6]),(0,[z286,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z76,z6]),(0,[z0,z1,z3,z287,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z223,z0,z1,z3,z4,z18,z6]),(0,[z288,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z289]),(0,[z0,z1,z290,z3,z4,z5,z6]),(0,[z0,z1,z178,z3,z4,z5,z14]),(0,[z0,z1,z3,z4,z5,z291,z6])],[(1,[z7,z8,z3,z4,z5,z6]),(0,[z292,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z293,z3,z4,z5,z6]),(0,[z294,z0,z1,z3,z4,z5,z6]),(0,[z102,z0,z1,z3,z5,z6,z119])],[(0,[z0,z1,z3,z4,z114,z5,z6]),(0,[z0,z295,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z114,z65,z6]),(0,[z0,z1,z3,z4,z296,z5,z6]),(0,[z0,z1,z3,z4,z297,z5,z6])],[(0,[z0,z1,z3,z4,z5,z23,z6]),(0,[z0,z298,z1,z3,z4,z5,z6]),(0,[z0,z1,z299,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z300,z5,z6]),(1,[z13,z0,z1,z73,z4,z5])],[(0,[z301,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z246,z4,z146,z5,z6])],[(1,[z87,z0,z3,z4,z6,z101]),(0,[z0,z1,z302,z3,z4,z5,z6]),(0,[z0,z1,z3,z303,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z304])]],
   [[(0,[z0,z1,z285,z3,z4,z5,z6]),(0,[z0,z305,z1,z3,z4,z5,z6]),(0,[z0,z1,z306,z3,z4,z5,z6]),(0,[z307,z0,z1,z3,z4,z5,z6]),(0,[z308,z0,z1,z3,z4,z5,z6]),(0,[z102,z309,z1,z3,z4,z5,z6]),(0,[z0,z310,z1,z3,z4,z5,z6]),(0,[z311,z0,z1,z3,z4,z5,z6]),(1,[z0,z88,z36,z1,z3,z4])],[(0,[z0,z1,z3,z4,z312,z5,z6]),(0,[z0,z1,z3,z313,z4,z5,z6]),(0,[z0,z1,z314,z3,z4,z5,z6]),(0,[z87,z0,z1,z3,z4,z5,z6])],[(0,[z0,z315,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z316,z4,z5,z6]),(0,[z1,z3,z251,z4,z26,z5,z6]),(1,[z0,z1,z3,z4,z5,z317]),(0,[z0,z1,z3,z4,z318,z5,z6]),(0,[z104,z0,z1,z3,z148,z4,z5])],[(0,[z0,z1,z3,z4,z5,z6,z319]),(1,[z0,z1,z3,z4,z5,z132]),(0,[z0,z1,z320,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z321]),(0,[z322,z0,z1,z3,z4,z5,z6])],[],[(0,[z323,z0,z1,z3,z4,z5,z6]),(1,[z63,z1,z64,z4,z5,z6]),(0,[z0,z1,z3,z324,z4,z5,z6]),(0,[z0,z325,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z326,z5,z6]),(0,[z0,z1,z3,z4,z74,z5,z14]),(0,[z0,z1,z3,z4,z5,z6,z327]),(0,[z0,z328,z1,z3,z4,z5,z6])],[(0,[z0,z1,z329,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z330,z6]),(0,[z331,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z332,z4,z5,z6]),(0,[z333,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z180,z5,z6])]],
   [[(0,[z0,z1,z334,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z335]),(0,[z0,z59,z1,z105,z3,z5,z6]),(0,[z0,z1,z3,z336,z4,z5,z6])],[(0,[z38,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z337,z5,z6]),(0,[z277,z0,z1,z64,z4,z5,z6]),(0,[z0,z1,z338,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z339,z6])],[(0,[z17,z0,z1,z3,z4,z114,z6]),(0,[z0,z1,z340,z3,z4,z5,z6]),(1,[z0,z325,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z341,z5,z6])],[(0,[z0,z1,z3,z251,z4,z5,z6]),(0,[z0,z24,z3,z4,z5,z6,z25]),(0,[z130,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z22]),(0,[z0,z1,z3,z4,z5,z6,z342])],[(0,[z7,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z343,z5,z6])],[(0,[z27,z0,z344,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z345,z6]),(0,[z0,z1,z3,z4,z346,z5,z6]),(0,[z0,z36,z1,z3,z4,z5,z14])],[(0,[z0,z182,z3,z4,z5,z6,z25]),(0,[z277,z0,z1,z3,z4,z118,z6]),(0,[z0,z1,z3,z347,z4,z5,z6]),(0,[z348,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z236,z4,z6,z128])],[(0,[z349,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z350]),(0,[z0,z3,z4,z74,z5,z6,z25]),(1,[z0,z1,z178,z4,z5,z14]),(0,[z0,z351,z1,z3,z4,z5,z6])]],
   [[(0,[z66,z0,z8,z3,z4,z5,z6]),(0,[z352,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z353,z4,z5,z6]),(0,[z354,z0,z1,z3,z4,z5,z6])],[(0,[z223,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z355,z4,z5,z6]),(0,[z0,z1,z356,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z357,z6]),(0,[z0,z1,z3,z4,z358,z5,z6])],[(1,[z0,z1,z3,z4,z359,z6]),(0,[z0,z360,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z361,z6]),(0,[z0,z1,z75,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z362,z5,z6])],[(0,[z0,z1,z3,z4,z5,z363,z6]),(0,[z0,z1,z64,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z18,z6,z101]),(0,[z0,z1,z3,z4,z364,z5,z6])],[(0,[z13,z0,z1,z64,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z118,z6]),(0,[z0,z1,z3,z365,z4,z5,z6]),(0,[z366,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z367,z4,z5,z6]),(0,[z0,z1,z3,z148,z5,z6,z22])],[(0,[z0,z1,z3,z89,z26,z5,z6]),(0,[z102,z104,z0,z1,z3,z5,z6]),(0,[z13,z0,z1,z73,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z368])],[(0,[z369,z0,z1,z3,z4,z5,z6]),(0,[z27,z1,z3,z4,z5,z6,z212]),(0,[z0,z1,z3,z4,z5,z6,z370]),(0,[z371,z0,z1,z3,z4,z5,z6]),(0,[z0,z372,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z373,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z374])],[(0,[z375,z0,z1,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z4,z376,z6]),(0,[z0,z1,z3,z4,z377,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z378]),(0,[z0,z379,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z380,z4,z5,z6]),(0,[z0,z1,z3,z4,z381,z5,z6]),(0,[z136,z0,z1,z3,z303,z4,z6]),(0,[z382,z0,z1,z3,z4,z5,z6]),(0,[z0,z383,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z384,z5,z6])],[],[(0,[z27,z0,z1,z3,z4,z218,z6]),(0,[z0,z385,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z386]),(0,[z0,z60,z1,z3,z4,z6,z101]),(0,[z0,z1,z3,z387,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z388,z6]),(0,[z0,z1,z389,z3,z4,z5,z6]),(0,[z0,z1,z390,z3,z4,z5,z6]),(0,[z391,z0,z1,z3,z4,z5,z6])],[(0,[z182,z1,z8,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z242,z5,z6]),(0,[z0,z191,z1,z3,z4,z5,z6]),(0,[z0,z1,z392,z3,z4,z5,z6]),(1,[z130,z0,z1,z3,z5,z6]),(0,[z0,z36,z229,z3,z4,z5,z6])],[(0,[z0,z393,z1,z3,z4,z5,z6]),(0,[z0,z1,z105,z3,z5,z6,z22]),(0,[z0,z1,z3,z394,z4,z5,z6])]],
   [[(0,[z395,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z396,z3,z4,z5,z6]),(0,[z0,z1,z3,z397,z4,z5,z6])],[(0,[z217,z277,z1,z3,z4,z5,z6]),(0,[z58,z0,z1,z3,z251,z5,z6]),(0,[z0,z1,z3,z4,z398,z5,z6]),(0,[z399,z0,z1,z3,z4,z5,z6]),(0,[z400,z0,z1,z3,z4,z5,z6]),(0,[z0,z401,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z402,z5,z6]),(0,[z217,z1,z3,z251,z4,z5,z6]),(0,[z0,z403,z1,z3,z4,z5,z6]),(1,[z58,z0,z3,z246,z5,z6]),(0,[z404,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z119]),(0,[z405,z0,z1,z3,z4,z5,z6])],[(0,[z0,z406,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z407,z4,z5,z6]),(0,[z0,z1,z3,z73,z4,z5,z25])],[(0,[z0,z1,z3,z4,z5,z408,z6]),(0,[z0,z1,z3,z409,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z410,z4,z5,z6]),(1,[z176,z1,z3,z4,z5,z28]),(0,[z0,z1,z3,z4,z5,z411,z6]),(0,[z0,z1,z3,z412,z4,z5,z6])],[(0,[z413,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z414,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z415,z5,z6]),(0,[z0,z1,z3,z416,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z417,z5,z6]),(0,[z58,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z418,z4,z5,z6]),(0,[z0,z1,z3,z4,z419,z5,z6]),(0,[z0,z1,z3,z420,z4,z5,z6])],[(1,[z0,z1,z3,z53,z5,z6])],[(0,[z0,z1,z3,z421,z4,z5,z6]),(0,[z0,z1,z97,z3,z4,z5,z6]),(0,[z0,z1,z3,z21,z4,z5,z22])],[(0,[z422,z0,z1,z3,z4,z5,z6]),(1,[z17,z1,z3,z4,z18,z6]),(0,[z0,z1,z3,z4,z114,z6,z37])],[(0,[z0,z1,z3,z4,z5,z6,z423]),(1,[z0,z134,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z424,z5,z6]),(0,[z0,z1,z3,z4,z425,z5,z6]),(0,[z0,z1,z3,z426,z4,z5,z6]),(0,[z0,z1,z3,z427,z4,z5,z6]),(0,[z0,z1,z3,z4,z74,z5,z6])],[(0,[z0,z428,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z359,z5,z6]),(0,[z0,z1,z3,z251,z5,z6,z22]),(0,[z0,z1,z3,z4,z5,z6,z429]),(0,[z0,z1,z3,z430,z4,z5,z6])],[(1,[z0,z1,z3,z80,z5,z6]),(0,[z0,z1,z3,z4,z5,z431,z6]),(1,[z0,z1,z432,z4,z5,z6])],[(0,[z38,z0,z182,z3,z4,z5,z6]),(0,[z223,z17,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z433]),(0,[z0,z1,z3,z434,z4,z5,z6]),(0,[z435,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z436,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z437]),(0,[z0,z1,z3,z4,z438,z5,z6])],[(0,[z0,z1,z439,z3,z4,z5,z6]),(0,[z0,z1,z3,z440,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z441]),(0,[z0,z1,z3,z442,z4,z5,z6]),(0,[z0,z1,z3,z443,z4,z5,z6]),(0,[z0,z1,z3,z4,z444,z5,z6])],[(0,[z7,z0,z182,z3,z4,z5,z6]),(0,[z0,z1,z3,z108,z4,z5,z6]),(0,[z445,z0,z1,z3,z4,z5,z6]),(0,[z217,z1,z3,z64,z4,z5,z6])],[(0,[z0,z1,z306,z3,z47,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z101]),(0,[z0,z1,z3,z446,z4,z5,z6]),(0,[z0,z447,z1,z3,z4,z5,z6]),(0,[z0,z448,z1,z3,z4,z5,z6]),(0,[z0,z36,z1,z3,z4,z5,z6])],[(0,[z449,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z450,z4,z5,z6]),(0,[z451,z0,z1,z3,z4,z5,z6])],[(0,[z92,z0,z1,z3,z4,z5,z6]),(0,[z0,z30,z50,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z452,z5,z6])],[(0,[z58,z0,z1,z3,z246,z5,z6]),(0,[z453,z0,z1,z3,z4,z5,z6]),(0,[z66,z0,z24,z3,z4,z5,z6]),(0,[z0,z454,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z455,z4,z5,z6]),(0,[z0,z1,z3,z456,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z457,z6]),(0,[z0,z1,z3,z4,z458,z5,z6]),(0,[z0,z1,z459,z3,z4,z5,z6])]],
   [[(0,[z460,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z461]),(0,[z0,z1,z3,z4,z462,z5,z6])],[(0,[z463,z0,z1,z3,z4,z5,z6]),(0,[z464,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z168,z4,z5,z6]),(0,[z0,z1,z465,z3,z4,z5,z6]),(0,[z104,z0,z1,z3,z4,z5,z22])],[(0,[z0,z1,z3,z466,z4,z5,z6]),(0,[z27,z0,z1,z3,z4,z237,z6]),(0,[z29,z0,z3,z47,z4,z5,z6]),(0,[z0,z1,z3,z467,z4,z5,z6])],[(0,[z0,z468,z1,z3,z4,z5,z6]),(0,[z0,z1,z469,z3,z4,z5,z6]),(0,[z87,z0,z3,z4,z5,z6,z101]),(1,[z0,z1,z3,z4,z470,z6])],[(0,[z0,z1,z3,z471,z4,z5,z6]),(0,[z27,z0,z1,z3,z4,z5,z212]),(0,[z0,z1,z3,z472,z4,z5,z6]),(1,[z0,z24,z3,z4,z5,z25]),(0,[z0,z1,z3,z236,z4,z5,z6])],[(1,[z277,z1,z147,z4,z5,z6]),(0,[z0,z59,z1,z3,z146,z5,z6]),(0,[z0,z1,z3,z148,z4,z5,z25]),(0,[z66,z0,z1,z3,z4,z74,z5])],[(0,[z217,z0,z1,z3,z26,z5,z6]),(0,[z0,z1,z75,z3,z4,z18,z6]),(0,[z136,z0,z1,z3,z4,z114,z6]),(0,[z0,z1,z3,z4,z5,z6,z317])],[(0,[z473,z0,z1,z3,z4,z5,z6]),(0,[z474,z0,z1,z3,z4,z5,z6]),(1,[z217,z1,z3,z251,z5,z6]),(0,[z0,z475,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z132]),(0,[z0,z476,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z59,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z261,z5,z6]),(0,[z0,z120,z1,z3,z4,z5,z6]),(0,[z0,z1,z477,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z478,z5,z6])],[(0,[z479,z0,z1,z3,z4,z5,z6]),(0,[z480,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z481,z5,z6]),(0,[z0,z1,z3,z482,z4,z5,z6]),(0,[z0,z1,z3,z483,z4,z5,z6])],[(0,[z0,z1,z3,z484,z4,z5,z6]),(0,[z0,z1,z3,z4,z485,z5,z6]),(0,[z0,z1,z3,z486,z4,z5,z6]),(0,[z0,z1,z3,z4,z74,z470,z6])],[(0,[z0,z1,z3,z4,z5,z487,z6]),(0,[z223,z1,z3,z4,z114,z5,z6]),(0,[z488,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z489])],[(0,[z490,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z491]),(0,[z0,z1,z3,z251,z5,z6,z119]),(0,[z0,z1,z3,z492,z4,z5,z6]),(0,[z0,z1,z3,z493,z4,z5,z6]),(0,[z0,z1,z3,z4,z146,z5,z6]),(0,[z0,z1,z3,z494,z4,z5,z6]),(0,[z0,z1,z3,z495,z4,z5,z6])],[(1,[z0,z1,z3,z337,z5,z6]),(0,[z104,z0,z1,z3,z251,z5,z6]),(0,[z176,z0,z1,z3,z4,z5,z28]),(0,[z87,z0,z1,z3,z4,z65,z6])],[(0,[z0,z1,z3,z4,z496,z5,z6]),(0,[z0,z1,z3,z4,z497,z5,z6]),(1,[z0,z59,z3,z146,z5,z6]),(0,[z0,z1,z3,z498,z4,z5,z6]),(0,[z0,z499,z1,z3,z4,z5,z6]),(0,[z0,z36,z1,z3,z73,z4,z5])],[(0,[z0,z1,z3,z4,z26,z5,z6]),(0,[z500,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z303,z4,z5,z76,z6])]],
   [[(0,[z501,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z502,z6]),(0,[z0,z503,z1,z3,z4,z5,z6]),(0,[z87,z0,z1,z75,z3,z4,z6])],[(0,[z504,z0,z1,z3,z4,z5,z6]),(0,[z505,z0,z1,z3,z4,z5,z6]),(0,[z506,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z507,z6])],[(0,[z508,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z509,z6]),(0,[z0,z233,z1,z3,z4,z5,z6]),(0,[z510,z0,z1,z3,z4,z5,z6]),(1,[z311,z0,z1,z4,z5,z6])],[(0,[z511,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z344,z3,z4,z5,z6]),(0,[z0,z512,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z513,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z514])],[(0,[z0,z1,z3,z4,z515,z5,z6]),(0,[z0,z1,z3,z516,z4,z5,z6]),(0,[z0,z1,z3,z517,z4,z5,z6]),(0,[z0,z518,z1,z3,z4,z5,z6]),(1,[z0,z233,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z519])],[(0,[z520,z0,z1,z3,z4,z5,z6]),(0,[z58,z0,z1,z105,z3,z5,z6])],[(0,[z277,z0,z1,z147,z4,z5,z6]),(0,[z0,z1,z3,z521,z4,z5,z6])]],
   [[(0,[z522,z0,z1,z3,z4,z5,z6]),(0,[z217,z92,z1,z3,z4,z5,z6]),(0,[z0,z1,z105,z3,z89,z5,z6])],[(0,[z0,z191,z1,z3,z47,z4,z6]),(0,[z0,z1,z3,z523,z4,z5,z6]),(0,[z0,z1,z524,z3,z4,z5,z6]),(0,[z0,z96,z1,z3,z236,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z128])],[(0,[z0,z1,z525,z3,z4,z5,z6])],[(1,[z0,z1,z306,z3,z4,z6]),(0,[z526,z0,z1,z3,z4,z5,z6]),(0,[z527,z0,z1,z3,z4,z5,z6]),(1,[z0,z229,z3,z4,z5,z6])],[(0,[z0,z1,z3,z528,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z529,z6]),(0,[z0,z1,z3,z4,z5,z6,z530]),(0,[z531,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z532,z4,z5,z6]),(0,[z176,z1,z3,z4,z5,z28,z6]),(0,[z0,z1,z533,z3,z4,z5,z6])],[(0,[z534,z0,z1,z3,z4,z5,z6]),(0,[z535,z0,z1,z3,z4,z5,z6]),(0,[z87,z136,z0,z1,z3,z4,z6]),(0,[z536,z0,z1,z3,z4,z5,z6])],[(0,[z0,z325,z1,z3,z47,z5,z6]),(0,[z102,z0,z1,z3,z89,z5,z6]),(0,[z0,z1,z3,z4,z537,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z538,z5,z6]),(0,[z0,z1,z3,z4,z5,z539,z6]),(0,[z0,z1,z3,z4,z540,z5,z6])],[(0,[z0,z24,z1,z3,z4,z5,z6]),(0,[z102,z0,z1,z4,z5,z6,z119]),(0,[z0,z1,z89,z4,z5,z6,z119]),(0,[z0,z1,z3,z541,z4,z5,z6])],[(0,[z63,z0,z1,z3,z4,z5,z6]),(0,[z223,z0,z1,z3,z4,z114,z6]),(0,[z0,z1,z3,z4,z5,z6,z542])],[(0,[z0,z1,z3,z543,z4,z5,z6]),(0,[z0,z1,z3,z544,z4,z5,z6]),(0,[z176,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z168,z4,z5,z6]),(0,[z0,z1,z3,z4,z545,z5,z6]),(0,[z546,z0,z1,z3,z4,z5,z6])],[(0,[z0,z182,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z547,z5,z6]),(0,[z0,z1,z3,z548,z4,z5,z6]),(0,[z0,z88,z1,z3,z4,z18,z6]),(0,[z0,z1,z75,z3,z4,z114,z6]),(0,[z0,z1,z3,z549,z4,z5,z6]),(0,[z58,z0,z3,z246,z4,z5,z6]),(0,[z0,z550,z1,z3,z4,z5,z6]),(1,[z104,z0,z1,z3,z148,z5])],[(0,[z0,z1,z8,z3,z4,z5,z6]),(0,[z0,z1,z3,z242,z4,z5,z6]),(0,[z29,z0,z1,z3,z4,z5,z317]),(0,[z0,z1,z3,z551,z4,z5,z6]),(0,[z0,z1,z552,z3,z4,z5,z6]),(0,[z0,z1,z3,z553,z4,z5,z6]),(0,[z104,z0,z1,z3,z21,z5,z6])],[(0,[z0,z554,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z251,z89,z5,z6]),(0,[z0,z1,z3,z555,z4,z5,z6]),(0,[z309,z0,z1,z3,z4,z5,z6])],[]],
   [[(0,[z0,z1,z3,z556,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z14,z25]),(0,[z0,z1,z3,z557,z4,z5,z6]),(0,[z0,z558,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z559,z4,z5,z6])],[(0,[z560,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z3,z561,z4,z5,z6]),(0,[z0,z562,z1,z3,z4,z5,z6]),(0,[z563,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z564,z4,z5,z6]),(0,[z565,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z285,z4,z5,z6]),(0,[z102,z0,z59,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z566,z5,z6]),(0,[z0,z1,z567,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z568,z6]),(1,[z125,z1,z3,z4,z5,z6]),(1,[z309,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z14,z37])],[(1,[z27,z1,z3,z4,z5,z212]),(0,[z0,z1,z3,z4,z5,z569,z6]),(0,[z0,z1,z3,z570,z4,z5,z6]),(1,[z136,z0,z1,z303,z4,z6]),(0,[z571,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z572]),(0,[z0,z1,z573,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z574]),(0,[z277,z0,z1,z3,z4,z359,z6])],[(0,[z0,z1,z3,z4,z5,z18,z6]),(0,[z0,z1,z3,z575,z4,z5,z6])]],
   [[],[(0,[z311,z0,z1,z148,z4,z5,z6])],[(0,[z576,z0,z1,z3,z4,z5,z6]),(0,[z0,z59,z1,z3,z4,z261,z5]),(0,[z0,z1,z3,z4,z577,z5,z6]),(0,[z136,z0,z1,z303,z4,z5,z6]),(0,[z0,z1,z3,z73,z4,z5,z37]),(0,[z0,z1,z3,z578,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z579]),(0,[z0,z1,z580,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z581]),(0,[z0,z1,z3,z582,z4,z5,z6]),(0,[z0,z1,z583,z3,z4,z5,z6]),(0,[z0,z1,z584,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z585]),(0,[z0,z1,z3,z4,z5,z6,z586])],[(0,[z0,z1,z3,z587,z4,z5,z6]),(0,[z0,z588,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z589]),(0,[z0,z1,z3,z4,z114,z6,z101]),(0,[z0,z1,z590,z3,z4,z5,z6]),(0,[z0,z591,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z592,z5,z6]),(0,[z0,z593,z1,z3,z4,z5,z6])],[(0,[z38,z0,z8,z3,z4,z5,z6]),(0,[z594,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z595]),(0,[z87,z116,z1,z3,z4,z5,z6])],[(0,[z0,z596,z1,z3,z4,z5,z6]),(0,[z136,z0,z1,z3,z4,z76,z6]),(0,[z0,z1,z597,z3,z4,z5,z6])],[(0,[z7,z38,z1,z3,z4,z5,z6]),(0,[z0,z1,z598,z3,z4,z5,z6]),(0,[z0,z599,z1,z3,z4,z5,z6])]],
   [[(1,[z0,z1,z3,z4,z5,z431]),(0,[z0,z59,z3,z4,z146,z5,z6])],[(0,[z0,z1,z3,z4,z5,z600,z6]),(0,[z601,z0,z1,z3,z4,z5,z6]),(0,[z27,z0,z1,z3,z57,z5,z6]),(1,[z66,z0,z3,z4,z74,z5]),(0,[z0,z1,z97,z3,z236,z4,z6])],[(0,[z0,z1,z3,z602,z4,z5,z6]),(0,[z0,z1,z603,z3,z4,z5,z6])],[(0,[z0,z1,z3,z604,z4,z5,z6]),(0,[z605,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z606])],[(0,[z223,z38,z1,z3,z4,z5,z6]),(0,[z63,z0,z1,z147,z4,z5,z6]),(0,[z607,z0,z1,z3,z4,z5,z6]),(0,[z87,z0,z1,z3,z4,z6,z37]),(0,[z0,z1,z3,z4,z608,z5,z6]),(0,[z0,z88,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z376,z6]),(0,[z609,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z610,z6]),(0,[z0,z1,z3,z4,z611,z5,z6])],[(0,[z0,z1,z3,z612,z4,z5,z6]),(0,[z0,z613,z1,z3,z4,z5,z6])],[(0,[z0,z614,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z615]),(0,[z136,z0,z60,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z616,z5,z6]),(0,[z112,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z277,z0,z1,z3,z4,z5,z6]),(1,[z0,z344,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z28,z6,z212]),(1,[z0,z1,z3,z582,z5,z6]),(0,[z617,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z376,z5,z6]),(0,[z0,z1,z3,z582,z47,z5,z6]),(0,[z87,z66,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z618,z5,z6]),(0,[z63,z0,z1,z3,z337,z5,z6]),(0,[z0,z88,z1,z3,z4,z114,z6]),(0,[z0,z1,z75,z3,z303,z4,z6]),(0,[z0,z1,z3,z4,z180,z6,z37])],[(0,[z0,z1,z3,z4,z5,z25,z22]),(0,[z0,z1,z3,z619,z4,z5,z6])],[(0,[z620,z0,z1,z3,z4,z5,z6]),(0,[z0,z621,z1,z3,z4,z5,z6]),(0,[z622,z0,z1,z3,z4,z5,z6]),(0,[z623,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z624,z4,z5,z6]),(0,[z625,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z115,z5,z6]),(0,[z0,z1,z3,z4,z626,z5,z6]),(0,[z0,z1,z627,z3,z4,z5,z6])],[(0,[z628,z0,z1,z3,z4,z5,z6]),(0,[z629,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z630,z5,z6])],[(0,[z0,z1,z3,z631,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z4,z5,z632,z6])]],
   [[(0,[z0,z1,z633,z3,z4,z5,z6]),(0,[z29,z0,z1,z3,z4,z5,z6]),(0,[z0,z30,z1,z3,z4,z5,z6]),(0,[z0,z1,z634,z3,z4,z5,z6]),(0,[z0,z1,z3,z21,z4,z5,z6])],[(0,[z0,z1,z635,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z636,z5,z6]),(0,[z29,z0,z1,z50,z4,z5,z6]),(0,[z0,z1,z637,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z638,z6])],[(0,[z87,z0,z60,z3,z4,z5,z6]),(0,[z0,z1,z3,z639,z4,z5,z6]),(0,[z640,z0,z1,z3,z4,z5,z6]),(0,[z0,z641,z1,z3,z4,z5,z6])],[(0,[z642,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z643]),(0,[z0,z1,z3,z4,z644,z5,z6])],[(0,[z0,z645,z1,z3,z4,z5,z6]),(0,[z0,z1,z646,z3,z4,z5,z6])],[(0,[z0,z647,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z648]),(0,[z649,z0,z1,z3,z4,z5,z6])],[(0,[z58,z0,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z650,z4,z5,z6]),(1,[z0,z1,z3,z4,z218,z6]),(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z102,z13,z0,z1,z4,z5,z6]),(0,[z652,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z653,z6])]],
   [[(0,[z29,z0,z1,z3,z4,z5,z431]),(0,[z654,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z655,z6]),(0,[z0,z36,z1,z3,z4,z180,z5])],[(0,[z0,z1,z656,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z657]),(0,[z0,z1,z3,z4,z658,z5,z6])],[(0,[z659,z0,z1,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z4,z23,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z3,z660,z4,z5,z6]),(0,[z0,z1,z661,z3,z4,z5,z6]),(0,[z0,z1,z662,z3,z4,z5,z6]),(1,[z0,z1,z105,z89,z5,z6])],[(0,[z1,z3,z64,z4,z26,z5,z6]),(0,[z663,z0,z1,z3,z4,z5,z6]),(0,[z664,z0,z1,z3,z4,z5,z6]),(0,[z665,z0,z1,z3,z4,z5,z6]),(0,[z0,z666,z1,z3,z4,z5,z6]),(0,[z0,z1,z667,z3,z4,z5,z6])],[(0,[z0,z1,z668,z3,z4,z5,z6]),(0,[z0,z60,z3,z4,z65,z5,z6]),(0,[z0,z1,z75,z3,z4,z76,z6])],[(0,[z0,z669,z1,z3,z4,z5,z6]),(1,[z0,z30,z50,z4,z5,z6]),(0,[z66,z0,z3,z4,z65,z5,z6]),(0,[z0,z1,z148,z432,z4,z5,z6]),(0,[z0,z670,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z671,z6]),(0,[z0,z1,z672,z3,z4,z5,z6]),(0,[z673,z0,z1,z3,z4,z5,z6])],[(0,[z674,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z675,z4,z5,z6]),(0,[z104,z0,z1,z3,z4,z5,z6]),(0,[z0,z88,z1,z3,z4,z180,z6])]],
   [[(0,[z102,z0,z1,z105,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z676]),(0,[z0,z1,z3,z677,z4,z5,z6])],[(0,[z277,z1,z147,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z678,z5,z6]),(0,[z0,z1,z3,z4,z237,z5,z6]),(0,[z679,z0,z1,z3,z4,z5,z6]),(1,[z116,z1,z3,z4,z5,z6])],[(0,[z680,z0,z1,z3,z4,z5,z6]),(0,[z681,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z75,z3,z4,z5,z31]),(0,[z0,z1,z3,z682,z4,z5,z6]),(0,[z0,z1,z97,z3,z5,z6,z128])],[(0,[z0,z1,z3,z4,z5,z6,z683]),(0,[z0,z1,z147,z4,z5,z6,z14]),(0,[z92,z0,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z684,z4,z5,z6]),(0,[z0,z685,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z74,z5,z22]),(0,[z0,z1,z3,z432,z4,z5,z6])],[(0,[z0,z1,z686,z3,z4,z5,z6]),(0,[z0,z1,z3,z687,z4,z5,z6]),(0,[z0,z3,z4,z65,z5,z6,z25]),(0,[z13,z0,z1,z178,z4,z5,z6])],[(0,[z0,z1,z3,z4,z688,z5,z6]),(0,[z0,z1,z3,z4,z5,z470,z6]),(0,[z0,z1,z73,z4,z5,z6,z14])],[(0,[z217,z0,z1,z3,z251,z5,z6]),(0,[z0,z134,z1,z3,z4,z5,z6]),(0,[z689,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z690,z4,z5,z6]),(0,[z0,z1,z691,z3,z4,z5,z6])],[(0,[z0,z1,z3,z692,z4,z5,z6]),(0,[z693,z0,z1,z3,z4,z5,z6]),(0,[z13,z0,z1,z3,z73,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z694])]],
   [[(0,[z0,z1,z695,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z696,z5,z6]),(0,[z0,z59,z1,z3,z251,z5,z6]),(0,[z697,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z698,z5,z6]),(0,[z0,z1,z3,z4,z180,z5,z37])],[(0,[z699,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z73,z53,z5,z6])],[(0,[z63,z277,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z700,z4,z5,z6])],[(0,[z38,z182,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z701,z4,z5,z6]),(0,[z0,z1,z702,z3,z4,z5,z6])],[(0,[z38,z0,z1,z3,z115,z5,z6]),(0,[z0,z1,z3,z4,z703,z5,z6]),(0,[z0,z704,z1,z3,z4,z5,z6]),(0,[z0,z705,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z21,z5,z22])],[(0,[z13,z0,z1,z147,z4,z5,z6])],[(0,[z0,z1,z706,z3,z4,z5,z6]),(1,[z29,z0,z47,z4,z5,z6]),(1,[z0,z1,z3,z236,z6,z128])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z707,z5,z6]),(0,[z0,z1,z3,z4,z708,z5]),(0,[z0,z1,z709,z4,z5,z6]),(0,[z0,z24,z3,z4,z5,z25]),(0,[z710,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z711]),(0,[z0,z1,z3,z57,z218,z6])],[(0,[z217,z1,z3,z692,z5,z6]),(0,[z1,z3,z251,z712,z5,z6]),(0,[z0,z475,z3,z4,z65,z6])],[(0,[z0,z1,z3,z4,z5,z713]),(0,[z217,z1,z3,z251,z5,z6]),(0,[z29,z0,z47,z4,z5,z317]),(0,[z102,z0,z1,z434,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z714,z6]),(0,[z0,z1,z3,z715,z5,z6]),(0,[z0,z134,z168,z4,z5,z6]),(0,[z29,z0,z191,z47,z4,z6]),(0,[z58,z0,z3,z716,z5,z6]),(0,[z0,z1,z3,z717,z4,z6]),(0,[z0,z1,z3,z4,z718,z6])],[],[(0,[z0,z1,z3,z4,z5,z719]),(0,[z0,z1,z3,z4,z720,z6]),(0,[z0,z721,z3,z4,z5,z6]),(0,[z0,z1,z168,z80,z5,z6]),(0,[z722,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z723,z6]),(0,[z0,z1,z3,z4,z724,z6]),(0,[z725,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z726,z6]),(0,[z0,z1,z3,z727,z5,z6]),(0,[z1,z3,z712,z4,z5,z6]),(0,[z510,z1,z3,z251,z5,z6]),(1,[z0,z1,z5,z6,z728])]],
   [[(0,[z0,z729,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z730,z6]),(0,[z0,z1,z285,z4,z218,z6]),(0,[z731,z1,z3,z4,z5,z6])],[(0,[z38,z260,z3,z4,z5,z6]),(0,[z39,z1,z64,z4,z5,z6]),(0,[z0,z732,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z317]),(0,[z0,z3,z716,z4,z5,z6]),(0,[z0,z733,z3,z4,z5,z6]),(0,[z0,z1,z5,z6,z728,z119]),(0,[z734,z0,z3,z4,z5,z6]),(0,[z735,z1,z3,z4,z5,z6])],[(0,[z27,z1,z3,z4,z218,z212]),(0,[z0,z1,z3,z4,z5,z132]),(0,[z0,z59,z3,z146,z5,z6]),(0,[z0,z1,z3,z4,z736,z6]),(0,[z0,z1,z3,z737,z21,z5])],[(0,[z0,z738,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z739,z5,z6]),(0,[z0,z1,z740,z4,z5,z6]),(0,[z0,z741,z3,z4,z5,z6]),(0,[z0,z1,z742,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z743]),(0,[z0,z1,z3,z4,z744,z6])],[(0,[z38,z1,z3,z4,z23,z6]),(0,[z63,z1,z64,z4,z5,z6]),(0,[z277,z1,z314,z4,z5,z6]),(0,[z623,z1,z3,z4,z18,z6]),(0,[z0,z1,z3,z4,z218,z6]),(0,[z88,z120,z1,z3,z4,z6]),(0,[z0,z1,z89,z5,z6,z728]),(0,[z0,z1,z745,z3,z4,z180])],[(0,[z7,z8,z3,z4,z376,z6]),(0,[z63,z1,z64,z242,z5,z6]),(0,[z0,z1,z3,z4,z5,z746]),(0,[z0,z1,z3,z747,z5,z6]),(0,[z0,z1,z3,z748,z4,z5])],[(0,[z1,z3,z4,z114,z749,z6]),(0,[z0,z1,z3,z4,z5,z750])]],
   [[(0,[z0,z751,z3,z4,z5,z6]),(0,[z435,z1,z3,z4,z18,z6]),(0,[z0,z60,z414,z3,z4,z6]),(1,[z0,z1,z752,z4,z5])],[(0,[z0,z325,z1,z3,z5,z6]),(0,[z0,z325,z1,z306,z3,z6]),(0,[z333,z0,z3,z4,z74,z5]),(0,[z0,z1,z753,z4,z5,z6]),(1,[z0,z1,z3,z737,z5])],[(1,[z754,z3,z4,z5,z6]),(0,[z0,z1,z3,z755,z5,z6]),(0,[z277,z1,z756,z4,z5,z6]),(0,[z1,z3,z4,z5,z28,z757]),(0,[z0,z3,z4,z758,z5,z6])],[(0,[z0,z1,z3,z4,z18,z31]),(0,[z27,z1,z3,z4,z5,z757])]],
   [[(0,[z0,z1,z3,z4,z759,z6]),(0,[z0,z1,z3,z760,z5,z6]),(0,[z0,z1,z761,z3,z4,z6])],[(0,[z0,z1,z762,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z763]),(0,[z1,z153,z3,z4,z18,z6]),(0,[z764,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z716,z5,z6])],[(0,[z0,z1,z3,z4,z5,z765]),(0,[z0,z1,z3,z4,z766,z6]),(0,[z0,z1,z767,z4,z5,z6]),(0,[z120,z1,z3,z4,z6,z37]),(0,[z0,z3,z4,z5,z6,z768]),(0,[z102,z172,z0,z1,z5,z6]),(0,[z0,z1,z178,z4,z5,z14])],[(0,[z0,z1,z3,z769,z5,z6]),(0,[z277,z1,z147,z4,z118,z6]),(0,[z0,z1,z306,z3,z4,z6]),(0,[z0,z1,z3,z770,z5,z6])]],
   [[(0,[z116,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z757]),(0,[z0,z1,z3,z4,z5,z771]),(0,[z120,z3,z4,z5,z6,z25]),(0,[z66,z0,z3,z4,z74,z470])],[(0,[z0,z1,z3,z772,z5,z6]),(0,[z0,z1,z3,z4,z773,z6]),(0,[z0,z1,z774,z4,z5,z6]),(0,[z0,z96,z1,z3,z770,z6])],[(0,[z0,z1,z3,z4,z359,z6]),(0,[z0,z1,z3,z775,z5,z6]),(0,[z0,z1,z3,z776,z5,z6]),(0,[z0,z207,z3,z4,z74,z5]),(0,[z777,z0,z1,z3,z4,z6])],[(0,[z778,z0,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z779,z4,z5]),(0,[z563,z1,z3,z251,z5,z6]),(0,[z0,z310,z3,z4,z5,z25]),(0,[z0,z1,z3,z4,z470,z14]),(0,[z125,z1,z4,z5,z6,z14]),(0,[z0,z36,z1,z3,z639,z4]),(0,[z0,z1,z3,z737,z5,z22])],[(0,[z1,z3,z208,z26,z5,z6]),(0,[z0,z1,z780,z4,z5,z6]),(0,[z87,z0,z3,z4,z345,z6]),(0,[z404,z0,z1,z73,z4,z5])],[(0,[z0,z1,z3,z781,z4,z5]),(0,[z0,z782,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z783,z6]),(0,[z0,z1,z3,z4,z784,z6]),(0,[z785,z1,z3,z4,z5,z6]),(0,[z87,z0,z3,z523,z4,z6]),(0,[z0,z1,z3,z4,z5,z786]),(0,[z787,z1,z3,z4,z5,z6]),(0,[z788,z1,z3,z4,z5,z6]),(0,[z0,z789,z3,z4,z5,z6]),(0,[z0,z1,z559,z4,z5,z14]),(1,[z0,z1,z790,z4,z6])]],
   [[(0,[z0,z791,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z792,z6]),(0,[z13,z130,z0,z1,z5,z6])],[(0,[z0,z1,z3,z4,z793,z6]),(0,[z0,z3,z4,z794,z5,z6]),(0,[z1,z3,z4,z5,z6,z795]),(0,[z0,z1,z745,z3,z4,z6])],[(0,[z0,z1,z3,z4,z796,z6]),(0,[z0,z1,z797,z4,z5,z6]),(0,[z0,z798,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z799,z6]),(0,[z0,z800,z1,z3,z5,z6])],[(0,[z801,z0,z3,z4,z5,z6]),(0,[z87,z0,z704,z3,z4,z6]),(0,[z102,z309,z1,z5,z6,z119]),(0,[z102,z0,z1,z644,z5,z6])]],
   [[(0,[z0,z1,z3,z802,z4,z5]),(0,[z803,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z804,z6]),(0,[z805,z1,z3,z4,z5,z6]),(0,[z136,z0,z1,z353,z4,z6]),(0,[z66,z0,z3,z4,z806,z5])],[(0,[z29,z0,z47,z4,z5,z6]),(0,[z87,z0,z3,z4,z6,z187]),(0,[z807,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z808,z5,z6]),(0,[z0,z809,z1,z3,z4,z6]),(0,[z0,z1,z3,z810,z5,z6]),(0,[z0,z1,z3,z148,z737,z5])],[(0,[z0,z1,z811,z4,z5,z6]),(0,[z0,z812,z1,z3,z4,z5]),(0,[z1,z3,z4,z749,z18,z6]),(0,[z0,z134,z3,z57,z5,z6]),(0,[z0,z1,z3,z4,z813,z6]),(0,[z29,z0,z774,z4,z5,z6]),(0,[z0,z1,z3,z814,z5,z6]),(0,[z0,z1,z3,z815,z5,z6])]],
   [[(0,[z125,z1,z3,z4,z5,z6]),(0,[z816,z1,z3,z4,z5,z6]),(0,[z58,z125,z1,z3,z5,z6])],[(0,[z554,z1,z3,z4,z18,z6]),(0,[z1,z756,z64,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z817]),(0,[z27,z1,z3,z4,z5,z212]),(0,[z27,z1,z3,z4,z237,z212]),(0,[z1,z3,z4,z5,z757,z212]),(0,[z29,z0,z582,z47,z5,z6]),(0,[z0,z1,z3,z818,z5,z6]),(0,[z0,z1,z4,z819,z5,z6]),(0,[z0,z820,z3,z4,z5,z6]),(0,[z0,z1,z436,z4,z5,z14]),(0,[z104,z0,z1,z148,z432,z5])],[(0,[z0,z1,z3,z4,z23,z6]),(0,[z0,z3,z774,z4,z5,z6]),(0,[z0,z229,z3,z73,z4,z5])],[(0,[z0,z1,z3,z4,z821,z6]),(0,[z0,z1,z3,z4,z822,z5]),(0,[z0,z59,z3,z146,z5,z132]),(0,[z823,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z31])]],
   [[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z824,z4,z5,z6]),(0,[z0,z1,z3,z825,z5,z6]),(0,[z0,z1,z3,z4,z237,z6]),(0,[z176,z1,z3,z4,z5,z28]),(0,[z136,z120,z1,z3,z4,z6]),(0,[z0,z3,z4,z806,z5,z6]),(0,[z0,z1,z603,z3,z148,z5])],[(0,[z0,z1,z3,z826,z5,z6]),(0,[z0,z1,z3,z242,z5,z6]),(0,[z63,z1,z64,z337,z5,z6]),(1,[z1,z756,z4,z5,z6]),(1,[z0,z3,z4,z6,z768]),(0,[z0,z60,z1,z3,z4,z31]),(0,[z13,z0,z1,z752,z4,z5])],[(0,[z0,z134,z285,z4,z5,z6]),(0,[z176,z1,z3,z4,z5,z757]),(0,[z29,z0,z47,z4,z5,z431]),(0,[z0,z1,z3,z827,z5,z6]),(0,[z0,z60,z3,z4,z65,z6]),(0,[z0,z3,z4,z6,z768,z101]),(0,[z0,z3,z4,z65,z6,z768]),(0,[z0,z518,z3,z4,z5,z25]),(0,[z0,z1,z105,z5,z6,z728])],[(0,[z0,z1,z3,z4,z828,z6]),(0,[z0,z1,z3,z4,z5,z829]),(0,[z0,z830,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z831,z6])]],
   [[(0,[z0,z1,z3,z832,z4,z5]),(0,[z92,z1,z3,z712,z5,z6]),(0,[z0,z1,z285,z80,z5,z6]),(0,[z0,z1,z105,z3,z5,z132]),(0,[z833,z1,z3,z4,z5,z6]),(0,[z102,z125,z1,z5,z6,z119])],[(0,[z0,z1,z3,z834,z5,z6]),(1,[z1,z3,z4,z5,z757]),(0,[z87,z120,z3,z4,z6,z101])],[(0,[z66,z0,z3,z4,z696,z5]),(0,[z17,z1,z3,z4,z18,z6]),(0,[z0,z1,z835,z4,z5,z6]),(0,[z104,z125,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z836,z6]),(0,[z0,z1,z3,z837,z5,z6]),(0,[z0,z1,z3,z4,z838,z6]),(0,[z0,z1,z3,z839,z5,z6]),(0,[z0,z3,z4,z806,z5,z25]),(0,[z0,z36,z1,z745,z3,z4])]],
   [[(0,[z0,z840,z3,z4,z5,z6]),(0,[z0,z1,z168,z57,z5,z6]),(0,[z0,z1,z3,z4,z5,z431]),(0,[z0,z1,z3,z4,z261,z5]),(0,[z0,z229,z3,z4,z5,z14])],[(0,[z38,z182,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z841,z6]),(0,[z0,z1,z3,z842,z5,z6]),(0,[z0,z1,z3,z843,z5,z6]),(0,[z0,z1,z3,z4,z5,z844]),(0,[z0,z1,z3,z4,z845,z6]),(0,[z66,z0,z3,z4,z74,z5]),(0,[z846,z1,z3,z4,z5,z6]),(0,[z847,z1,z3,z4,z5,z6]),(0,[z0,z1,z432,z4,z5,z6]),(0,[z0,z1,z3,z737,z5,z6])],[(0,[z0,z1,z3,z4,z848,z6]),(0,[z0,z849,z3,z4,z5,z6]),(0,[z0,z850,z3,z4,z5,z6]),(0,[z0,z1,z3,z851,z5,z6])],[(0,[z0,z1,z3,z852,z5,z6]),(0,[z92,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z5,z853]),(0,[z0,z1,z854,z3,z5,z6]),(0,[z0,z1,z3,z855,z4,z5]),(0,[z0,z1,z3,z53,z5,z25]),(0,[z856,z0,z1,z3,z5,z6]),(0,[z0,z1,z73,z752,z4,z5])]],
   [[(0,[z754,z8,z3,z4,z5,z6]),(0,[z0,z857,z1,z3,z4,z6]),(0,[z0,z59,z3,z544,z5,z6]),(0,[z17,z1,z3,z4,z749,z6]),(0,[z1,z3,z4,z5,z6,z858]),(0,[z0,z1,z3,z4,z859,z6]),(1,[z0,z3,z716,z5,z6])],[(0,[z0,z1,z3,z4,z376,z6]),(0,[z0,z1,z860,z4,z5,z6]),(0,[z0,z1,z3,z4,z861,z6]),(0,[z0,z1,z3,z862,z4,z6]),(0,[z0,z1,z863,z4,z5,z6])],[(0,[z864,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z865,z5,z6]),(0,[z866,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z867,z5,z6]),(0,[z0,z1,z3,z868,z5,z6]),(0,[z0,z1,z75,z85,z4,z76])]],
   [[(0,[z7,z8,z3,z4,z23,z6]),(0,[z0,z869,z1,z3,z4,z5]),(0,[z0,z1,z870,z4,z5,z6]),(0,[z0,z1,z3,z582,z5,z6]),(0,[z0,z1,z3,z4,z5,z871]),(0,[z102,z0,z1,z5,z6,z728])],[(0,[z0,z344,z285,z4,z5,z6]),(0,[z27,z1,z168,z4,z5,z212]),(0,[z0,z30,z774,z4,z5,z6])],[(0,[z7,z8,z3,z4,z5,z6]),(0,[z1,z8,z3,z4,z23,z6]),(0,[z0,z1,z872,z4,z5,z6]),(0,[z102,z0,z1,z3,z5,z132]),(0,[z125,z1,z3,z89,z5,z6]),(0,[z0,z1,z4,z5,z6,z728])],[(0,[z0,z873,z1,z3,z4,z5]),(0,[z13,z0,z1,z700,z4,z5]),(0,[z1,z3,z4,z749,z5,z6]),(0,[z0,z1,z3,z874,z5,z6])]],
   [[(0,[z0,z1,z3,z115,z5,z6]),(0,[z0,z1,z3,z875,z5,z6]),(0,[z0,z1,z3,z876,z5,z6]),(0,[z0,z1,z3,z712,z5,z6]),(0,[z39,z0,z1,z5,z6,z119]),(0,[z0,z877,z3,z4,z5,z6]),(0,[z0,z1,z3,z251,z5,z132]),(0,[z0,z1,z168,z4,z237,z6]),(0,[z0,z1,z3,z4,z5,z878]),(0,[z879,z1,z3,z4,z5,z6]),(0,[z0,z880,z3,z4,z5,z6]),(0,[z881,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z882,z5,z6]),(0,[z0,z1,z3,z4,z883,z6]),(0,[z0,z1,z3,z53,z74,z5]),(0,[z0,z884,z3,z4,z5,z6]),(0,[z13,z0,z1,z73,z4,z5])],[(0,[z0,z1,z3,z4,z885,z6]),(0,[z0,z1,z3,z4,z886,z6]),(0,[z0,z1,z3,z887,z4,z5]),(0,[z0,z1,z3,z4,z470,z6]),(0,[z102,z0,z1,z5,z6,z119]),(0,[z0,z888,z1,z3,z4,z6]),(0,[z0,z889,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z890,z6]),(0,[z0,z1,z3,z891,z5,z6]),(0,[z892,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z893,z6]),(0,[z87,z0,z3,z4,z6,z101]),(0,[z0,z894,z3,z4,z5,z6]),(0,[z0,z1,z75,z790,z4,z6]),(0,[z311,z104,z0,z1,z148,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z895]),(0,[z0,z1,z3,z4,z5,z896]),(0,[z277,z1,z147,z4,z5,z6]),(0,[z0,z897,z3,z4,z5,z6]),(0,[z0,z1,z75,z430,z4,z6]),(0,[z0,z60,z3,z4,z341,z6]),(0,[z0,z1,z51,z4,z5,z14]),(0,[z0,z898,z3,z4,z5,z6]),(0,[z0,z88,z36,z1,z3,z4])],[(0,[z0,z1,z3,z899,z5,z6]),(0,[z900,z0,z1,z4,z5,z6]),(0,[z0,z344,z3,z80,z5,z6]),(0,[z0,z1,z3,z901,z4,z5]),(0,[z0,z902,z3,z4,z5,z6]),(0,[z0,z1,z752,z4,z5,z14])],[(0,[z0,z1,z3,z4,z903,z6]),(0,[z0,z1,z3,z904,z5,z6]),(0,[z0,z1,z3,z905,z5,z6]),(0,[z0,z906,z3,z4,z5,z6]),(0,[z0,z1,z432,z4,z74,z5])],[]],
   [[(0,[z0,z1,z3,z4,z5,z907]),(0,[z0,z1,z3,z908,z5,z6]),(0,[z0,z1,z3,z4,z5,z909])],[(0,[z38,z182,z3,z115,z5,z6]),(0,[z182,z754,z3,z4,z5,z6]),(0,[z0,z910,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z911,z6]),(0,[z0,z1,z3,z4,z5,z912]),(0,[z0,z913,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z914]),(0,[z915,z1,z3,z4,z5,z6]),(0,[z0,z3,z246,z716,z5,z6])],[(0,[z0,z1,z3,z4,z5,z916]),(0,[z277,z1,z3,z337,z5,z6]),(0,[z0,z1,z3,z917,z5,z6]),(0,[z125,z59,z1,z3,z5,z6]),(0,[z125,z1,z3,z5,z6,z22])],[(0,[z673,z8,z3,z4,z5,z6]),(0,[z0,z918,z3,z4,z5,z6]),(0,[z405,z1,z3,z26,z5,z6]),(0,[z0,z1,z3,z4,z919,z6]),(0,[z0,z1,z920,z4,z5,z6]),(0,[z921,z1,z3,z4,z5,z6]),(0,[z0,z1,z97,z3,z770,z6])]],
   [[(0,[z0,z1,z3,z337,z5,z6]),(0,[z271,z0,z3,z4,z6,z101]),(0,[z0,z325,z191,z1,z3,z6]),(0,[z922,z1,z3,z4,z5,z6]),(0,[z923,z1,z3,z4,z5,z6])],[(0,[z0,z1,z4,z924,z5,z6]),(0,[z0,z1,z3,z4,z925,z6]),(0,[z0,z1,z3,z4,z6,z768]),(0,[z0,z1,z3,z926,z5,z6]),(0,[z66,z0,z233,z3,z4,z6])],[(0,[z0,z50,z774,z4,z5,z6]),(0,[z0,z60,z3,z4,z6,z768]),(0,[z0,z448,z3,z4,z5,z25]),(0,[z0,z1,z105,z89,z5,z6]),(0,[z0,z1,z790,z4,z76,z6])],[(0,[z0,z1,z3,z4,z927,z6]),(0,[z0,z928,z1,z3,z5,z6]),(0,[z66,z120,z3,z4,z5,z6]),(0,[z0,z1,z3,z929,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z930,z6]),(0,[z223,z1,z3,z4,z749,z6]),(0,[z0,z344,z168,z4,z5,z6]),(0,[z0,z1,z3,z4,z931,z5]),(0,[z0,z1,z3,z932,z4,z6]),(1,[z0,z3,z4,z806,z5]),(0,[z136,z0,z1,z790,z4,z6]),(0,[z0,z1,z933,z4,z5,z6])],[(0,[z0,z1,z3,z934,z5,z6]),(0,[z0,z1,z756,z4,z5,z6]),(0,[z0,z134,z3,z4,z218,z6]),(0,[z0,z30,z50,z4,z5,z6]),(0,[z935,z1,z3,z4,z5,z6]),(0,[z13,z0,z1,z4,z5,z156]),(0,[z0,z1,z3,z737,z4,z5])],[(0,[z87,z0,z1,z3,z4,z31]),(0,[z311,z0,z1,z4,z5,z6]),(0,[z0,z1,z105,z478,z5,z6]),(1,[z0,z1,z745,z3,z4])],[(0,[z0,z406,z3,z4,z5,z25]),(0,[z0,z1,z936,z4,z5,z6]),(0,[z0,z1,z937,z4,z5,z6]),(0,[z0,z1,z3,z80,z218,z6]),(0,[z87,z0,z533,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z938])]],
   [[(0,[z0,z3,z4,z939,z5,z6]),(0,[z0,z1,z3,z4,z5,z940]),(0,[z0,z1,z941,z4,z5,z6]),(0,[z942,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z943,z5,z6]),(0,[z0,z233,z1,z3,z4,z6]),(0,[z944,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z945,z6]),(0,[z274,z182,z3,z4,z5,z6]),(0,[z1,z3,z756,z4,z5,z6]),(0,[z946,z0,z1,z3,z5,z6]),(0,[z0,z1,z947,z4,z5,z6]),(0,[z0,z1,z3,z948,z5,z6]),(0,[z0,z1,z3,z4,z5,z949]),(0,[z0,z59,z3,z146,z261,z5]),(0,[z0,z1,z790,z4,z5,z6])],[(0,[z0,z1,z3,z950,z4,z5]),(0,[z112,z0,z88,z3,z4,z6])],[(0,[z0,z1,z951,z4,z5,z6]),(0,[z120,z1,z3,z4,z6,z101]),(0,[z0,z1,z394,z89,z5,z6])]],
   [[(0,[z0,z1,z3,z952,z5,z6]),(0,[z0,z1,z3,z4,z5,z953]),(0,[z0,z1,z3,z4,z180,z37])],[(0,[z0,z1,z3,z954,z5,z6]),(1,[z1,z3,z712,z5,z6]),(0,[z664,z1,z3,z26,z5,z6])],[(0,[z0,z1,z3,z108,z5,z6]),(0,[z0,z1,z955,z4,z5,z6]),(0,[z956,z0,z1,z4,z5,z6]),(0,[z42,z1,z64,z4,z5,z6]),(0,[z0,z1,z202,z89,z5,z6]),(0,[z0,z1,z3,z957,z5,z6]),(0,[z0,z59,z290,z3,z5,z6]),(0,[z58,z0,z3,z416,z5,z6]),(0,[z0,z229,z3,z4,z5,z6])],[(0,[z269,z1,z3,z4,z18,z6]),(0,[z223,z1,z3,z4,z312,z6]),(0,[z1,z3,z64,z337,z5,z6]),(0,[z0,z958,z1,z3,z4,z5]),(0,[z0,z191,z1,z3,z4,z6]),(0,[z0,z59,z3,z716,z5,z6]),(0,[z959,z1,z3,z4,z5,z6]),(0,[z0,z1,z745,z3,z4,z5])]],
   [[(0,[z38,z754,z3,z4,z5,z6]),(0,[z0,z960,z3,z4,z5,z6]),(0,[z29,z0,z306,z47,z4,z6]),(0,[z0,z550,z3,z4,z65,z6]),(0,[z0,z1,z3,z770,z236,z6])],[(0,[z0,z1,z3,z4,z749,z6]),(0,[z0,z1,z961,z3,z5,z6]),(0,[z130,z0,z1,z5,z6,z14])],[(0,[z0,z88,z129,z1,z3,z4]),(0,[z0,z1,z168,z4,z218,z6]),(0,[z0,z1,z285,z57,z5,z6]),(0,[z0,z1,z3,z962,z5,z6]),(0,[z0,z1,z3,z963,z4,z6]),(0,[z13,z0,z1,z73,z53,z5])],[(0,[z0,z1,z75,z4,z678,z6]),(0,[z0,z1,z3,z964,z5,z6]),(0,[z0,z1,z3,z73,z4,z470]),(0,[z13,z125,z1,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z728]),(0,[z0,z88,z1,z745,z3,z4])]],
   [[(0,[z0,z1,z3,z4,z965,z6]),(0,[z0,z966,z3,z4,z5,z6]),(0,[z0,z1,z967,z4,z5,z6]),(0,[z136,z0,z1,z660,z4,z6]),(0,[z0,z344,z3,z4,z218,z6]),(0,[z27,z1,z3,z57,z5,z212]),(0,[z0,z3,z4,z74,z806,z5]),(0,[z112,z0,z88,z36,z3,z4])],[(0,[z0,z968,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z969,z5]),(0,[z0,z1,z3,z970,z5,z6]),(0,[z209,z1,z147,z4,z5,z6]),(0,[z217,z1,z3,z712,z5,z6]),(0,[z0,z971,z3,z4,z5,z6]),(0,[z0,z1,z972,z4,z5,z6]),(0,[z125,z1,z3,z5,z6,z119]),(0,[z104,z0,z1,z3,z5,z156]),(0,[z0,z1,z3,z21,z5,z22]),(0,[z311,z104,z0,z1,z5,z6])],[(0,[z0,z1,z3,z973,z5,z6]),(0,[z974,z0,z1,z4,z5,z6]),(0,[z0,z975,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z976,z6]),(0,[z0,z1,z4,z977,z5,z6]),(0,[z978,z1,z3,z4,z5,z6]),(0,[z130,z0,z1,z3,z5,z6]),(0,[z102,z0,z1,z5,z6,z142])],[(0,[z38,z182,z3,z108,z5,z6]),(0,[z0,z1,z3,z979,z5,z6]),(0,[z0,z1,z3,z57,z5,z6]),(0,[z0,z1,z3,z980,z5,z6]),(0,[z0,z1,z3,z57,z237,z6]),(0,[z0,z1,z3,z236,z6,z128]),(0,[z104,z0,z1,z3,z148,z5])]],
   [[(0,[z7,z754,z3,z4,z5,z6]),(0,[z0,z1,z3,z981,z5,z6]),(0,[z63,z1,z756,z4,z5,z6]),(0,[z0,z3,z716,z146,z5,z6]),(1,[z0,z1,z3,z770,z6])],[(0,[z0,z1,z3,z982,z5,z6]),(0,[z1,z3,z712,z26,z5,z6]),(0,[z983,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z498,z5,z22]),(0,[z0,z1,z3,z85,z4,z5])],[(0,[z1,z754,z3,z4,z5,z6]),(0,[z120,z1,z3,z4,z5,z6]),(0,[z58,z0,z3,z246,z5,z6]),(0,[z0,z984,z3,z4,z5,z6])],[(0,[z0,z1,z220,z4,z5,z14]),(0,[z0,z3,z4,z985,z5,z6]),(0,[z27,z1,z285,z4,z5,z212]),(0,[z120,z1,z3,z4,z65,z6]),(0,[z0,z1,z3,z482,z5,z22]),(0,[z104,z0,z1,z3,z737,z5])]],
   [[(0,[z0,z1,z3,z26,z5,z132]),(0,[z223,z1,z3,z4,z114,z6]),(0,[z0,z774,z47,z4,z5,z6]),(0,[z0,z1,z3,z4,z986,z6]),(0,[z0,z1,z3,z752,z4,z5]),(0,[z0,z1,z597,z73,z4,z5])],[(0,[z0,z1,z987,z4,z5,z6]),(0,[z0,z1,z3,z770,z6,z128])],[(0,[z0,z1,z285,z4,z5,z6]),(0,[z1,z147,z756,z4,z5,z6]),(0,[z0,z1,z3,z373,z5,z22]),(0,[z0,z1,z285,z4,z237,z6]),(0,[z0,z1,z3,z4,z5,z988])],[(0,[z0,z1,z989,z4,z5,z6]),(0,[z309,z1,z3,z4,z5,z6]),(0,[z120,z1,z75,z3,z4,z6]),(0,[z0,z1,z752,z4,z5,z6])]],
   [[(0,[z0,z990,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z991]),(0,[z136,z0,z1,z303,z4,z6]),(0,[z0,z1,z303,z790,z4,z6])],[(0,[z0,z1,z4,z992,z5,z6]),(0,[z0,z1,z993,z4,z5,z6]),(0,[z27,z134,z3,z4,z5,z212]),(0,[z0,z1,z3,z4,z5,z994]),(0,[z0,z1,z3,z4,z5,z995]),(0,[z0,z1,z3,z53,z5,z6]),(0,[z0,z96,z1,z97,z3,z6])],[(0,[z996,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z458,z37]),(0,[z112,z0,z3,z4,z6,z37])],[(0,[z277,z1,z147,z4,z359,z6]),(0,[z27,z1,z3,z80,z5,z212]),(0,[z997,z1,z3,z4,z5,z6]),(0,[z87,z116,z3,z4,z6,z101]),(0,[z0,z1,z745,z3,z4,z37])]],
   [[(0,[z0,z1,z998,z4,z5,z6]),(0,[z0,z134,z3,z4,z5,z6]),(0,[z0,z1,z999,z3,z4,z6]),(0,[z104,z0,z1,z3,z440,z5]),(0,[z0,z134,z3,z4,z237,z6]),(0,[z0,z1000,z1,z3,z4,z6]),(0,[z1001,z1,z3,z4,z5,z6]),(0,[z0,z1,z1002,z4,z5,z6]),(0,[z0,z1,z3,z4,z806,z5]),(0,[z0,z1,z75,z4,z76,z31])],[(0,[z0,z1,z3,z4,z1003,z6]),(0,[z0,z1004,z1,z3,z4,z6]),(0,[z0,z1,z75,z4,z76,z6])],[(0,[z0,z1,z3,z80,z5,z6]),(0,[z0,z1,z3,z80,z237,z6]),(0,[z66,z0,z233,z3,z4,z74])],[(0,[z0,z344,z3,z57,z5,z6]),(0,[z1,z3,z4,z5,z6,z757]),(0,[z0,z1,z3,z1005,z5,z6]),(0,[z29,z0,z325,z47,z5,z6]),(0,[z87,z0,z3,z4,z6,z768])]],
   [[(0,[z0,z1,z3,z4,z1006,z6]),(0,[z0,z1,z1007,z4,z5,z6]),(0,[z0,z1,z3,z4,z114,z31]),(0,[z531,z1,z3,z4,z114,z6]),(0,[z102,z0,z1,z10,z5,z6]),(0,[z311,z0,z1,z5,z6,z22]),(0,[z0,z88,z36,z229,z3,z4])],[(0,[z0,z1008,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1009]),(0,[z0,z1,z105,z701,z5,z6]),(0,[z0,z1,z3,z4,z1010,z6])],[(0,[z0,z1,z3,z1011,z5,z6]),(0,[z474,z1,z3,z26,z5,z6]),(0,[z151,z1,z3,z26,z5,z6]),(0,[z500,z1,z3,z251,z5,z6]),(1,[z1,z3,z4,z749,z6]),(0,[z0,z1,z3,z4,z417,z37]),(0,[z0,z1,z3,z4,z5,z1012]),(0,[z0,z1,z3,z4,z5,z1013]),(0,[z0,z88,z1,z3,z4,z155]),(0,[z0,z1,z3,z4,z106,z37])],[(0,[z0,z1,z3,z1014,z5,z6]),(0,[z0,z1,z3,z790,z4,z6]),(0,[z0,z1,z3,z1015,z5,z6]),(0,[z1016,z0,z1,z4,z5,z6])]],
   [[(0,[z271,z8,z3,z4,z5,z6]),(0,[z0,z1,z3,z1017,z4,z6]),(0,[z201,z1,z3,z26,z5,z6]),(0,[z94,z1,z3,z4,z18,z6]),(0,[z1018,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1019,z5]),(0,[z0,z1,z178,z752,z4,z5])],[(0,[z0,z754,z3,z4,z5,z6]),(0,[z0,z134,z3,z80,z5,z6]),(1,[z0,z774,z4,z5,z6]),(0,[z0,z1,z3,z4,z1020,z6]),(0,[z0,z1,z3,z770,z4,z6])],[(0,[z58,z0,z3,z684,z5,z6]),(0,[z145,z1,z3,z4,z114,z6]),(0,[z0,z1,z306,z3,z582,z6]),(0,[z66,z0,z3,z4,z5,z155]),(0,[z0,z24,z3,z4,z806,z5])],[(0,[z0,z1,z3,z1021,z4,z6]),(0,[z0,z1,z3,z4,z5,z1022]),(0,[z0,z191,z1,z3,z582,z6]),(0,[z112,z0,z3,z4,z5,z6]),(0,[z13,z130,z0,z1,z73,z5])]],
   [[(0,[z0,z1,z1023,z4,z5,z6]),(0,[z0,z1,z3,z4,z1024,z6]),(0,[z0,z1,z1025,z4,z5,z6]),(0,[z400,z1,z3,z4,z114,z6]),(0,[z27,z344,z3,z4,z5,z212]),(0,[z1026,z1,z3,z4,z5,z6]),(0,[z0,z1027,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1028,z5]),(0,[z0,z1,z168,z4,z5,z6])],[(0,[z0,z1029,z3,z4,z5,z6]),(0,[z0,z1,z3,z1030,z5,z6])],[(0,[z0,z344,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z118,z6]),(0,[z0,z1,z1031,z4,z5,z6]),(0,[z0,z344,z3,z4,z237,z6]),(0,[z0,z233,z3,z4,z6,z25]),(0,[z0,z1,z432,z4,z5,z25])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 562) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 562).take 448) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1010)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [562, 448] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 103).take 25).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [103, 25] = true :=
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

end PEqualNP.Outside.L_meta_46060

theorem PEqualNP.Outside.L_meta_46060 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4242589824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4242589824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46060.solve