# Lubridate allows us to extract information regarding & manipulate calendar dates

library(tidyverse)
library(lubridate)

wday(today()) # provides position of day in week (e.g. 1 = Sunday, 2 = Monday, etc.)
yday(dmy(01032020)) # position of day in year (e.g. 61)

day(dmy(01032020)) # extracts 'day' of date 
month(dmy(01032020)) # extracts 'month' of date 
year(dmy(01032020)) # extracts 'year' of date 

difference = dmy(01032020) - dmy(28022020) # provides difference between days