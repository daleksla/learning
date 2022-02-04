# Data analysis is important allowing us to identify trends & patterns
# Equally, visualising data gives us a clear idea of what the information means by giving it visual context through maps or graphs, as-well as clearly showing outliers within large data sets
# Both makes the data more natural for the human mind to comprehend then just an endless quantity of data
# Note: whilst a correlation co-efficient is always calculatable, if the visual chart is clearly non-linear than there is no drawable conclusion
# Note: clear outliers / anomalies, which are more easily noticed visually, must be removed to purposefully to calculate proper standard deviation & correlation

library(tidyverse)
library(gapminder)
library(ISLR) # provides us with the dataset 'Credit'
library(GGally) # library extension of 'ggplot2' - contains templates for advanced & different plots

### Below we measure the scatterplot and correlation between two variables (bi-variate data) ###

data = filter(gapminder, country == "Albania")

# RECAP - 'summary()' provides statistics for each column such as mean, median, ranges (min, IQR's, max etc.)
summary(data$gdpPercap) # provide summary statistics for 'gdpCapcap' column - remember we can use '$' symbol instead of index!
# alternatively, we could use the 'pull()' function to pull the column as a vector, however that would involve creating un-needed variables
# gdpCap = pull(data, gdpPercap)
summary(data$lifeExp)

r = cor(data$gdpPercap, data$lifeExp) # 'cor()' calculates the correlation between two lists of values
ggplot(data=data, mapping=aes(x=gdpCap, y=lifeExp)) + geom_point()
cat("Correlation between GDP p/ CAP & LIFE EXPECTANCY: ", r, "\n")
cat("Standard deviation of 'lifeExp' category: ", sd(data$lifeExp), "\n") # 'sd()' calculates the standard deviation for a given vector

### Below we measure the scatterplot and correlation between more than two variables at once (multi-variate data) ###

creditTibble = as_tibble(Credit) # convert dataset to Tibble
creditTibble = select(creditTibble, Balance, Limit, Income) # get tibble with specified columns
ggscatmat(creditTibble) 
# 'ggscatmat()' function makes a scatterplot matrix for quantitative variables with density plots
# it automatically provides a scatterplot and a correlation coefficient, together with a smoothed histogram for each variable
