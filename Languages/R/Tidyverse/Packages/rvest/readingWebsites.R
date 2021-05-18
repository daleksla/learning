# The R tidyverse package “rvest” (think harvest) provides functions for parsing webpages
# We need to tell it which web page to load, where to “look” on the page (particular HTML tags) and how to extract the data in a usable format

library(tidyverse)
library(rvest) 
url = "http://espn.go.com/nfl/superbowl/history/winners"
page = read_html(url) # get HTML of page
sb_table = html_nodes(page, 'table') # get data within 'table' elements 
sb = html_table(sb_table)[[1]] # parse table into data-frame & get first table (note: table will wrap due to size)

print(sb) # this will the extracted table from the web

# Note: this would not lead to optimum analysis, therefore we need to ultimately standardised this into a Tibble format
#...this is accomplished in 'R/Tidyverse/Tibbles/optimising.R'