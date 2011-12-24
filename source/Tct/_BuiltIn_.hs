builtInProcessors :: P.AnyProcessor
builtInProcessors = 
    P.SomeProcessor timeout 
    P.<|>
    P.SomeProcessor popstar 
    P.<|>
    P.SomeProcessor ppopstar 
    P.<|>
    P.SomeProcessor lmpo 
    P.<|>
    P.SomeProcessor bounds 
    P.<|>
    P.SomeProcessor fail 
    P.<|>
    P.SomeProcessor success 
    P.<|>
    P.SomeProcessor empty 
    P.<|>
    P.SomeProcessor open 
    P.<|>
    P.SomeProcessor ite 
    P.<|>
    P.SomeProcessor best 
    P.<|>
    P.SomeProcessor fastest 
    P.<|>
    P.SomeProcessor sequentially 
    P.<|>
    P.SomeProcessor epostar 
    P.<|>
    P.SomeProcessor matrix 
    P.<|>
    P.SomeProcessor arctic 
    P.<|>
    P.SomeProcessor poly 
    P.<|>
    P.SomeProcessor (S.StdProcessor irr)
    P.<|>
    P.SomeProcessor (S.StdProcessor composeRC)
    P.<|>
    P.SomeProcessor (S.StdProcessor weightgap)
    P.<|>
    P.SomeProcessor (S.StdProcessor compose)
    P.<|>
    P.SomeProcessor (S.StdProcessor dependencyPairs)
    P.<|>
    P.SomeProcessor (S.StdProcessor removeTail)
    P.<|>
    P.SomeProcessor (S.StdProcessor simpDPRHS)
    P.<|>
    P.SomeProcessor (S.StdProcessor simpKP)
    P.<|>
    P.SomeProcessor (S.StdProcessor usableRules)
    P.<|>
    P.SomeProcessor (S.StdProcessor pathAnalysis)
    P.<|>
    P.SomeProcessor (S.StdProcessor uncurry)
    P.<|>
    foldr (P.<|>) P.none Preds.predicateProcessors
