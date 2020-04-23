zipn n = do
    vs <- replicateM n (newName "vs")
    [| \f ->
        $(lamE (map varP vs)
            [| getZipList $
                $(foldl
                    (\a b -> [| $a <*> $b |])
                    [| pure f |]
                    (map (\v -> [| ZipList $(varE v) |]) vs))
            |])
     |]