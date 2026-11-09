Abbreviation foo x := false.

Check (match true with foo _ => 0 | _ => 1 end).

Abbreviation bar x := (@false).

Check (match true with bar _ => 0 | _ => 1 end).

Fail Check (match true with foo => 0 | _ => 1 end).
