import Distribution.Simple
import Distribution.Simple.Setup
import Distribution.Simple.Utils (rawSystemExit)

main = defaultMainWithHooks simpleUserHooks
        { preBuild = \a b -> makeGlucose a b >> preBuild simpleUserHooks a b }

makeGlucose _ flags = 
    rawSystemExit (fromFlag $ buildVerbosity flags) "sh"
        ["-c", "(cd ./glucose/simp; LIB=glucose make libr)"]
