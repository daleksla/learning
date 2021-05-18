# In R, datasets presented to us may require further polishing to prevent mis-interpretation
# For example, integers may indicate the status of an occurance and are thus 'categorical' (as opposed to having numeric value)
# This file will explore scrubbing / cleaning data

library(tidyverse)
library(titanic) # contains dataset we'll analyse

titanic = as_tibble(titanic_train) # import as tibble
titanic = select(titanic,Survived,Pclass,Name,Gender=Sex,Age,Fare) # note: we import column 'Sex' as 'Gender'
summary(titanic) 

# note: this will show analysis on columns holding numerical data but that are categorical - this is a problem
# (e.g.) column 'Survived' holds 0 as false, 1 as true
# Therefore, let's convert them as categorical variables
titanic$Survived = as_factor(titanic$Survived) # 'as_factor()' converts a variable into a factor, but preserves variable and value label
titanic$Pclass = as_factor(titanic$Pclass)

summary(titanic) # now, the latter two modified columns present as tallies, rather then ranges, etc.

# We can now also plot this data effectively
ggplot(data = titanic, mapping = aes(x=Gender)) + geom_bar(mapping=aes(fill=Survived)) 
# plot as bar-chart, where x-axis is male and female & the colour within each bar dependant on the status of each that survived
ggplot(data = titanic, aes(x=Gender)) + geom_bar(aes(fill=Survived)) + facet_wrap(~Pclass) 
# By simply adding + facet_wrap(~<category>) to our plot we can create a multi-panel plot dedicated to one plot per <category>
# 3 passanger class', therefore 3 bar charts showing which Men and women survived for a certain class