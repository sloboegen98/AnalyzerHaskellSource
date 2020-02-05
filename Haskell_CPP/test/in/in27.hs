module MyInstances() where  
    instance Show (a -> b) where  
      show fn = "<<function>>"  
    instance Show (IO a) where  
      show io = "<<IO action>>"