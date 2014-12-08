import Distribution.Simple
import Distribution.Simple.Setup
import Distribution.Simple.Utils (rawSystemExit)

main = defaultMainWithHooks simpleUserHooks
        { preConf = \a b -> do
            makeGlucose a b
            makeGlucoseWrapper a b
            makePeriploWrapper a b
            preConf simpleUserHooks a b
        }

makeGlucose _ flags = 
    rawSystemExit (fromFlag $ configVerbosity flags) "sh"
        ["-c", "(cd ./glucose/simp; LIB=glucose make libr)"]

makeGlucoseWrapper _ flags =
    rawSystemExit (fromFlag $ configVerbosity flags) "make"
        ["--directory=glucose_wrapper"]

makePeriploWrapper _ flags =
    rawSystemExit (fromFlag $ configVerbosity flags) "make"
        ["--directory=periplo_wrapper"]
