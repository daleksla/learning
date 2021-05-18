# The R tidyverse package “dplyr” (pronounced “DEE-ply-er”) is a powerful package
# It manipulates, cleans and summarises structured data
# It makes data exploration and data manipulation easy and fast in R
# dplyr allows us to extract rows based on logical criteria and columns based on column names

library(tidyverse)
# install.packages("nycflights13") # run only once - it's just a dataset we're using
library(nycflights13)
names(flights) #display column names of dataset

# Row selection
# We can select rows based on index values
slice(flights, 87:96) # including 87 & 96
top_n(flights, 20) # top 20 row entries

# We can get rows using conditional & logical operators (ie. where a specific condition matches)
# (where conditional operations include <, >, <=, >= and logical operations include !, &, |)
filter(flights, month==1, day==1) # only those rows for which the month column is 1 and the day column is 1
filter(flights, dep_time <= 0600) # only for flights for which deparated between 00:00AM and 06:00AM (inc.)
filter(flights, dest == "IAH" | dest == "HOU") # only for flights destined to Houston's IAH or HOU