# In R, 'Lubridate' is a library used to create, manipulate and format dates & timestamps into formal structures (as opposed to strings etc.)

library(tidyverse)
library(lubridate)

today() # provides todays date

dmy(01032020) # formats numbers provided as day, month, year
ymd(20200301) # formats numbers provided as year, month, day
# all other major permutations etc. 

ymd_h("2010-04-14-04") # formats string provided as year, month, day, hour
ymd_hm("2010-04-14-04-35") # formats string provided as year, month, day, hour, minute
ymd_hms("2010-12-13 15:30:30") #... there are also other ways we can layout a function
ymd_hms("2010-04-14-04-35-59") # formats string provided as year, month, day, hour, minute, second
dmy_hms("14-04-2010-04-35-59") # formats string provided as day, month, year, hour, minute, second
# and other major permutations etc. 

with_tz("2009-08-07 00:00:01", tz = "America/New_York") # converts a UTC datetime & returns a datetime as it would appear in a different time zone