data XX = St String
        | In Int

fun :: XX -> String
fun xx = let (St s) = xx in if s=="A" then "Yo" else "No"

