module KMIConverter where

import VTable.Compliation.Conversion

main = do 
    print "start convert KMI"
    sortKMI
    print "finish sort"
    convertKMI
    print "finished!"
