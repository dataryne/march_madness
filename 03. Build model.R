
##--------------------------------------------
## march madness prediction
## Section looks at performance of models while varying three things: 1) the variable being predicted. It's either the score difference
    # or a 0/1 (where 1 means the strong seed wins). 2) the data included in the model (how home/away games are weighted, variables
    # included, how many of the most recent games, etc). and 3) the learning method (linear regression, decision trees, svm, knn).

##--------------------------------------------

##-----Load libraries-----
library(logging)
library(DBI)
library(RSQLite)
library(dplyr)
library(tidyr)
library(reshape2)
library(ggplot2)
library(rpart)
#library(rattle)
library(rpart.plot)
library(RColorBrewer)
library(randomForest)
library(party)
library(e1071)
library(class)
library(gmodels)
library(gridExtra)
library(grid)

##########################################################################
###############   Section 1. Set up
##########################################################################


##-----Define functions-----
get_log_filename = function(){
  log_file_name = format(Sys.time(), format="MarchMad_log_%Y_%m_%d_%H%M%S.log")
  return(log_file_name)
}


add_to_log <- function(model_run,number_correct,short_description="",first_of_round=FALSE){
  
  if (first_of_round == TRUE){
    loginfo(paste('--------------------------------'))
    loginfo(short_description)
  }
  loginfo(paste(model_run,":",number_correct))
}

# LOAD TABLE FROM DB
get_table_from_basketball <- function(table_to_get){
  myQuery <- dbSendQuery(con, paste("SELECT * FROM",table_to_get))
  the_table <- dbFetch(myQuery, n = -1)
  dbClearResult(myQuery)
  return(the_table)
}

add_team_names <- function(dataset){
  team_names_subset <- team_names %>% distinct(Team_Id,CleanName) %>% select(Team_Id,CleanName)
  dataset <- merge(dataset,team_names_subset %>% rename(SS_Name=CleanName),
                   by.x="SS_team",by.y="Team_Id",all.x=TRUE)
  dataset <- merge(dataset,team_names_subset %>% rename(WS_Name=CleanName),
                   by.x="WS_team",by.y="Team_Id",all.x=TRUE)
  return(dataset)
}


# CLEAN COMPACT TOURNEY RESULTS
# This function takes in the compact tourney results and does the following: filters to certain seasons, adds different ways to measure a win, 
  # adds the team names, adds team seeds, and rounds (and can subset to round 0, round 1 or all rounds)
clean_tourney_results <- function(tourney_results,season_cutoff,win_tracker,round_to_return){
  tourney_results <- tourney_results %>% select(-index)#,-StrongSeed)
  
  # Add ways to measure win
  # - score_diff
  tourney_results <- tourney_results %>% filter(Season > season_cutoff)  %>% mutate(Score_diff=SS_score - WS_score)
  # - 0 or 1
  if (win_tracker[2]==1){
    tourney_results$SS_Win <- ifelse(tourney_results$Score_diff > 0,1,0)  
  }
  # - 1 or -1
  if (win_tracker[3]==1){
    tourney_results$SS_Win_alt <- ifelse(tourney_results$Score_diff > 0,1,-1)
  }
  
  if (win_tracker[1] == 0){
    tourney_results <- tourney_results %% select(-Score_diff)
  }
  
  # Get the team names
  team_names_subset <- team_names %>% distinct(Team_Id,CleanName) %>% select(Team_Id,CleanName)
  tourney_results <- merge(tourney_results,team_names_subset %>% rename(SS_Name=CleanName),
                           by.x="SS_team",by.y="Team_Id",all.x=TRUE)
  tourney_results <- merge(tourney_results,team_names_subset %>% rename(WS_Name=CleanName),
                           by.x="WS_team",by.y="Team_Id",all.x=TRUE)
  
  # Get seeds
  # seeds_subset <- seeds %>% filter(Season > season_cutoff) %>% select(Season,Team,SeedNum,Region)
  # tourney_results <- merge(tourney_results,seeds_subset %>% rename(SS_SeedNum=SeedNum,SS_region=Region),
  #                          by.x=c("Season","SS_team"),by.y=c("Season","Team"),all.x=TRUE)
  # tourney_results <- merge(tourney_results,seeds_subset %>% rename(WS_SeedNum=SeedNum,WS_region=Region),
  #                          by.x=c("Season","WS_team"),by.y=c("Season","Team"),all.x=TRUE)
  
  # Subset to Round 1
  # slots_subset <- slots %>% filter(Season > season_cutoff) %>% select(Season,Round,Strongseed,Weakseed,Slot)
  # tourney_results <- merge(tourney_results,slots_subset,by.x=c("Season","SS_Seed","WS_Seed"),by.y=c("Season","Strongseed","Weakseed"),all=TRUE)
  tourney_results$Round <- ifelse(tourney_results$Daynum %in% c(134,135),0,tourney_results$Round)
  if (round_to_return == 1){
    return(round1_results <- tourney_results %>% filter(Round == 1))
    #round0_results <- tourney_results %>% filter(Round == 0)
  }
  else if (round_to_return > 1){
    return(tourney_results %>% filter(Round != 0))
  }
  else {
    return(tourney_results)
  }
}

# AGGREGATE THE GAME DATA.
# - weight_away_diff: 2/3 will weight the away games as 2/3 and home games as 1/3 in the mean. Enter -1 to not weight by home/away
# - take_last_X_games: only include the last X games in the mean. Enter -1 to take the whole season.
aggregate_game_data <- function(game_dataset,weight_away_diff,take_last_X_games=-1){
  #put a few checks in place on inputs
  stopifnot(weight_away_diff==-1|(weight_away_diff > 0 & weight_away_diff < 1))
  stopifnot(take_last_X_games==-1|(take_last_X_games > 0))
  
  # filter to regular season and drop a few variables I wont need
  game_dataset <- game_dataset %>% filter(TournamentGame == 0) %>%  select(-index,-Date,-Opp,-Win,-TournamentGame)
  
  # only keep the last X games if desired. if = -1, take all games
  if (take_last_X_games != -1){
    game_dataset <- game_dataset %>% arrange(Year,Tm,desc(Day_Number))
    game_dataset <- do.call(rbind, by(game_dataset, list(game_dataset$Year, game_dataset$Tm), FUN=function(x) head(x, take_last_X_games)))
  }
  
  # drop Day Number
  game_dataset <- game_dataset %>% select(-Day_Number)
  
  # If going to weight away games more, do that here
  if (weight_away_diff != -1){
    game_dataset$Location[game_dataset$Location == "Neutral"] <- "Away" # Change neutral to away. No teams will have a true "Home" game in the tournament, 
    # so I am going to group home and away/neutral ("away") into separate groups and discount home games in the team averages. I am making the assumption that
    # away and neutral games will be more representative of tournament play and so should be weighted more heavily in the averages I calculate.
    away_weight <- weight_away_diff
    # calculate sum of all game statistics. Do it by Year, Team and Location
    game_data_agg_regseason <-game_dataset  %>% mutate(NumGames = 1) %>% group_by(Year,Tm,Location) %>% summarize_each(funs(sum))
    
    # drop the pcts since they are now meaningless after the aggregation
    game_data_agg_regseason <- game_data_agg_regseason[, -grep("pct$", colnames(game_data_agg_regseason))] # drop the pct columns 
    
    # melt to long format to make the next couple steps easier
    game_data_agg_regseason <- game_data_agg_regseason %>% melt(., 
                                                                variable.name = "Stat",
                                                                value.names = "Val",
                                                                id.vars = c("Year","Tm","Location"))#,"NumGames"))
    
    # weight home games as 1/3 and away games as 2/3 and then sum up by year and team
    game_data_agg_regseason$value <- ifelse(game_data_agg_regseason$Location=="Away",game_data_agg_regseason$value*away_weight,game_data_agg_regseason$value*(1-away_weight))
    game_data_agg_regseason <- game_data_agg_regseason %>% select(-Location) %>% group_by(Year,Tm,Stat) %>% summarize_each(funs(sum))
    
    # convert back to wide and then 
    game_data_agg_regseason <- dcast(game_data_agg_regseason, Year+Tm ~ Stat,value.var = "value")
  }
  
  # if not going to weight home/away differently
  else{
    game_data_agg_regseason <- game_dataset %>% mutate(NumGames = 1) %>% group_by(Year,Tm) %>% select(-Location) %>% summarize_each(funs(sum))
    
    # drop the pcts since they are now meaningless after the aggregation
    game_data_agg_regseason <- game_data_agg_regseason[, -grep("pct$", colnames(game_data_agg_regseason))] # drop the pct columns 
    
  }
  
  # re-calculate the percentages
  game_data_agg_regseason <- game_data_agg_regseason %>% mutate(Tm_FG_pct = Tm_FG / Tm_FGA,
                                                                Tm_3P_pct = Tm_3P / Tm_3PA,
                                                                Tm_FT_pct = Tm_FT / Tm_FTA,
                                                                Opp_FG_pct = Opp_FG / Opp_FGA,
                                                                Opp_3P_pct = Opp_3P / Opp_3PA,
                                                                Opp_FT_pct = Opp_FT / Opp_FTA)
  cols_to_divide <- unique (intersect(grep("_", colnames(game_data_agg_regseason)),grep("pct$", colnames(game_data_agg_regseason),invert=TRUE)))
  
  # divide all stats by number of games played to get average per game. Then drop number of games
  game_data_agg_regseason[, cols_to_divide] <- game_data_agg_regseason[, cols_to_divide]/game_data_agg_regseason$NumGames
  game_data_agg_regseason <- game_data_agg_regseason %>% select(-NumGames)
  
  return(game_data_agg_regseason)
}

# DO FINAL MODEL PREP
more_model_prep <- function(dataset,for_final_model=FALSE){
  # Remove score and numot. I'll be predicting score diff and dont want any other info from the game
  if (for_final_model==TRUE){
    dataset <- dataset %>% select(-SS_score,-WS_score,-WS_team,-SS_team,-Slot,-Round,-Winning_Seed)#-Numot,-loc,-SS_Seed,-WS_Seed 
  } else {
    dataset <- dataset %>% select(-SS_score,-WS_score,-SS_Seed,-WS_Seed,-WS_team,-SS_team,-Slot,-Round,-Winning_Seed)#-Numot,-loc
  }
  
  
  # convert all character variables to factors
  dataset <- as.data.frame(unclass(dataset))
  
  #convert more variables to factor
  dataset$Season <- as.factor(dataset$Season)
  #WS_Seed
  #SS_Seed
  # should be converted to ordered factors?
  return(dataset)
}

# ADD GAME DATA TO TOURNEY DATA
add_more_data <- function(dataset,infotoadd,ss_year_var,ws_year_var,ss_team_var,ws_team_var,for_final_model=FALSE){
  if(for_final_model== TRUE){
    temp_wlabs <- infotoadd %>% setNames(paste0("SS_",names(.)))
    temp_llabs <- infotoadd %>% setNames(paste0("WS_",names(.)))
    
    dataset <- merge(dataset,temp_wlabs, by.x=c("SS_Name"),by.y=c(ss_team_var),all.x=TRUE)
    dataset <- merge(dataset,temp_llabs, by.x=c("WS_Name"),by.y=c(ws_team_var),all.x=TRUE)
  } else{
    
  temp_wlabs <- infotoadd %>% setNames(paste0("SS_",names(.)))
  temp_llabs <- infotoadd %>% setNames(paste0("WS_",names(.)))
  
  dataset <- merge(dataset,temp_wlabs, by.x=c("Season","SS_Name"),by.y=c(ss_year_var,ss_team_var),all.x=TRUE)
  dataset <- merge(dataset,temp_llabs, by.x=c("Season","WS_Name"),by.y=c(ws_year_var,ws_team_var),all.x=TRUE)
  }
  return(dataset)
}


# set up train and test sets
get_test_data <- function(dataset,test_year,predicted_var){
  model_data <- more_model_prep(dataset)
  #model_data <- more_model_prep(round1_results_with_gameavgs) %>% select(-SS_Win,-SS_Win_alt)
  if (predicted_var==1){
    model_data$To_Predict <- model_data$Score_diff
  } else if(predicted_var==2){
    model_data$To_Predict <- model_data$SS_Win
  } else{
    model_data$To_Predict <- model_data$SS_Win_alt
  }
  model_data <- model_data %>% select(-Score_diff,-SS_Win,-SS_Win_alt)
  train <- model_data %>% filter(!Season %in% c(test_year,"2017")) %>% select(-WS_Name,-SS_Name)
  test <- model_data %>% filter(Season %in% test_year) %>% select(-WS_Name,-SS_Name)
  test_answers <- model_data %>% filter(Season %in% test_year) %>% select(Season,WS_Name,SS_Name,To_Predict)
  return(list(train,test,test_answers))
}

##-----Functions to Run models and return number of correct-----
# run a linear model. Only looks at score diff since wasn't working for 0 or 1 model
run_lm <- function(dataset,year){
  win_type = 1
  # set up train and test sets
  model_dat <- get_test_data(dataset,year,win_type)
  
  train <- model_dat[[1]]
  if("WS_Conf" %in% colnames(train)){
    train <- train %>% select(-WS_Conf)
  }
  if("Season" %in% colnames(train)){
    train <- train %>% select(-Season)
  }
  test <- model_dat[[2]]
  if("WS_Conf" %in% colnames(test)){
    test <- test %>% select(-WS_Conf)
  }
  if("Season" %in% colnames(test)){
    test <- test %>% select(-Season)
  }
  test_answers <- test %>% select(To_Predict)
  
  # fit a model and predict outcomees
  fit <- lm(To_Predict ~ ., data = train)
  pred_lm <- predict(fit,test)
  test_answers$Predicted <- pred_lm
  
  # get count of number of correct
  test_answers$Correct <- ifelse(sign(test_answers$To_Predict) == sign(test_answers$Predicted),1,0)
  return(nrow(test_answers %>% filter(Correct == 1)))
}

# run glm. Only looks at score diff since wasn't converging for 0/1 model
run_glm <- function(dataset,year,family_type="gaussian"){
  # set up train and test sets
  win_type = 1
  model_dat <- get_test_data(dataset,year,win_type)
  train <- model_dat[[1]]
  if("WS_Conf" %in% colnames(train)){
    train <- train %>% select(-WS_Conf)
  }
  if("Season" %in% colnames(train)){
    train <- train %>% select(-Season)
  }
  test <- model_dat[[2]]
  if("WS_Conf" %in% colnames(test)){
    test <- test %>% select(-WS_Conf)
  }
  if("Season" %in% colnames(test)){
    test <- test %>% select(-Season)
  }
  test_answers <- test %>% select(To_Predict)
  
  # fit a model and predict wins
  fit <- glm(To_Predict ~ ., family = family_type,data = train)
  pred_glm <- predict(fit,test)
  test_answers$Predicted <- pred_glm
  
  # get number of predictions that were correct
  test_answers$Correct <- ifelse(sign(test_answers$To_Predict) == sign(test_answers$Predicted),1,0)  
  
  return(nrow(test_answers %>% filter(Correct == 1)))
}

# run a basic decision tree
run_rpart <- function(dataset,fit_class,year,win_type,pred_class){
  model_dat <- get_test_data(dataset,year,win_type)
  #train <- model_dat[[1]]
  #test <- model_dat[[2]]
  test_answers <- model_dat[[3]]
  
  fit <- rpart(To_Predict ~ ., data=model_dat[[1]],method=fit_class) #"anova" or "class"
  #fancyRpartPlot(fit)
  pred <- predict(fit, newdata=model_dat[[2]], type=pred_class) #"vector"
  test_answers$Predicted <- pred
  if(win_type == 1){
    test_answers$Correct <- ifelse((test_answers$To_Predict < 0 & test_answers$Predicted < 0) | (test_answers$To_Predict > 0 & test_answers$Predicted > 0),1,0)
    #got 21 of 32 games right, which is not good (only 65%).   
  } else{
    test_answers$Predicted_RP <- ifelse(test_answers$Predicted >= .5,1,0)
    test_answers$Correct <- ifelse(test_answers$To_Predict == test_answers$Predicted_RP,1,0)
  }
  return(test_answers %>% select(Correct) %>% summarize(correct=sum(Correct)))
}

# run a random forest model
run_rforest <- function(dataset,year,win_type){
  model_dat <- get_test_data(dataset,year,win_type)
  train <- model_dat[[1]]
  test <- model_dat[[2]]
  test_answers <- model_dat[[3]]
  
  if(win_type == 1){
    fit <- randomForest(To_Predict ~ ., data=train, importance=TRUE) #ntree=2000
  } else {
    fit <- randomForest(as.factor(To_Predict) ~ ., data=train, importance=TRUE) #ntree=2000
  }
  varImpPlot(fit) #look at what variables were important
  plot(fit)
  rf_pred <- predict(fit,test)
  test_answers$Predicted_RF <- rf_pred
  
  if(win_type == 1){
    test_answers$Correct_RF <- ifelse((test_answers$To_Predict < 0 & test_answers$Predicted_RF < 0) | (test_answers$To_Predict > 0 & test_answers$Predicted_RF > 0),1,0)
    test_answers %>% select(Correct_RF) %>% summarize(Correct_RF=sum(Correct_RF))
  } else {
    test_answers$Correct_RF <- ifelse(test_answers$To_Predict == test_answers$Predicted_RF,1,0)
    test_answers %>% select(Correct_RF) %>% summarize(Correct_RF=sum(Correct_RF))
    
  }
  return(test_answers %>% select(Correct_RF) %>% summarize(correct=sum(Correct_RF)))
}

# run a support vector machine model
run_svm <- function(dataset,test_year){
  win_type = 2
  model_dat <- get_test_data(dataset,test_year,win_type)
  train <- model_dat[[1]]
  test <- model_dat[[2]]
  test_answers <- model_dat[[3]]
  
  # tune parameters for SVM
  tuneResult <- tune(svm, To_Predict ~ ., data=train,
                     ranges = list(epsilon = seq(0,1,0.1), cost = 2^(2:9))
  )
  #plot(tuneResult)
  
  fit <- svm(To_Predict ~ ., data=train,epsilon=tuneResult$best.parameters[1],cost=tuneResult$best.parameters[2])
  pred_svm <- predict(fit, test)
  test_answers$Predicted_SVM <- pred_svm
  test_answers$Predicted_SVM2 <- ifelse(test_answers$Predicted_SVM >= .5,1,0)
  return(nrow(test_answers %>% filter(Predicted_SVM2 == To_Predict)))
  
}

# run a k nearest neighbors model
run_knn <- function(dataset,test_year,k_val){
  win_type = 2
  model_dat <- get_test_data(dataset,test_year,win_type)
  train <- model_dat[[1]]
  test <- model_dat[[2]]
  
  
  model_datars <- rbind(train,test)
  ind <- ifelse(model_datars$Season==test_year,2,1)
  nums <- sapply(model_datars, is.numeric)
  model_datars <- model_datars[ , nums]
  
  num_cols <- length(model_datars)
  knn.training <- model_datars[ind==1, 1:num_cols-1]
  knn.test <- model_datars[ind==2, 1:num_cols-1]
  knn.train.labels <- model_datars[ind==1, num_cols]
  knn.test.labels <- model_datars[ind==2, num_cols]
  
  ##-----Figure out how what value to set k equal to-----
  accuracy <- rep(0, 60)
  k <- 1:60
  for(x in k){
    knn.pred <- knn(train=knn.training ,test=knn.test ,cl=knn.train.labels ,k=x)
    accuracy[x] <- mean(knn.pred == knn.test.labels)
  }
  plot(k, accuracy, type = 'b')
  # use at least 5 but maybe more
  k_val <- ifelse(which.max(accuracy) > k_val,which.max(accuracy),k_val)
  print(paste("k value:",k_val))
  knn.pred <- knn(train=knn.training ,test=knn.test ,cl=knn.train.labels ,k=k_val)
  #knn_answers <- as.data.frame(list(knn.test.labels,knn.pred))
  knn_answers <- data.frame(To_Predict = knn.test.labels,Predicted=knn.pred)
  knn_answers$Correct <- ifelse(knn_answers$To_Predict == knn_answers$Predicted,1,0)
  return(nrow(knn_answers %>% filter(Correct==1)))
}

# run all the models and log the results
run_all_models <- function(dataset,ss_team,ws_team,test_year,model_description){
  test_data <- get_test_data(dataset,test_year,2)[[2]]
  add_to_log("Total games",nrow(test_data),
             short_description=model_description,first_of_round=TRUE)
  add_to_log("Baseline, just picking SS",nrow(test_data %>% filter(To_Predict == 1)))
  add_to_log("lm, score diff", run_lm(dataset,test_year))
  add_to_log("glm, score diff", run_glm(dataset,test_year,"gaussian"))
  add_to_log("r part, score diff",run_rpart(dataset,"anova",test_year,1,"vector"))
  add_to_log("r part, 0 or 1",run_rpart(dataset,"anova",test_year,2,"vector"))
  add_to_log("random forest, score diff",run_rforest(dataset,test_year,1))
  add_to_log("random forest, 0 or 1",run_rforest(dataset,test_year,2))
  add_to_log("svm",run_svm(dataset,test_year))
  add_to_log("knn",run_knn(dataset,test_year,4))
  
  
}



run_all_models <- function(dataset,ss_team,ws_team,test_year,model_description,
                           results_df = data.frame( "Description" = character(), "lm_scorediff" = integer(), "glm_scorediff" = integer(), 
                                                    "rpart_scorediff" = integer(), "rpart_01" = integer(), "rforest_scorediff" = integer(),
                                                    "rforest_01" = integer(),"svm" = integer(), "knn" = integer(), stringsAsFactors=FALSE)){
  test_data <- get_test_data(dataset,test_year,2)[[2]]
  add_to_log("Total games",nrow(test_data),
             short_description=model_description,first_of_round=TRUE)
  add_to_log("Baseline, just picking SS",nrow(test_data %>% filter(To_Predict == 1)))
  
  lm_description <- "lm, score diff"
  lm_results <- run_lm(dataset,test_year)
  add_to_log(lm_description, lm_results)
  results_df
  glm_description <- "glm, score diff"
  glm_results <- run_glm(dataset,test_year,"gaussian")
  add_to_log(glm_results, glm_results)
  
  rpart_description_1 <- "r part, score diff"
  rpart_results_1 <- run_rpart(dataset,"anova",test_year,1,"vector")
  add_to_log(rpart_description_1, rpart_results_1)
  
  rpart_description_2 <- "r part, 0 or 1"
  rpart_results_2 <- run_rpart(dataset,"anova",test_year,2,"vector")
  add_to_log(rpart_description_2,rpart_results_2)
  
  rforest_desc <- "random forest, score diff"
  rforest_results <- run_rforest(dataset,test_year,1)
  add_to_log(rforest_desc,rforest_results)
  
  rforest_description_2 <- "random forest, 0 or 1"
  rforest_results_2 <- run_rforest(dataset,test_year,2)
  add_to_log(rforest_description_2,rforest_results_2)
  
  svm_description <- "svm"
  svm_results <- run_svm(dataset,test_year)
  add_to_log(svm_description,svm_results)
  
  knn_description <- "knn"
  knn_results <- run_knn(dataset,test_year,4)
  add_to_log(knn_description,knn_results)
  
  results_df[nrow(results_df)+1,] <- c(model_description,lm_results,glm_results,rpart_results_1,rpart_results_2,
                                       rforest_results,rforest_results_2,svm_results,knn_results)
  return(results_df)
}
##----Run Main Function Here----
#if(interactive()){

  
  ##----Setup Test Logger-----
  log_file_name = get_log_filename()
  basicConfig()
  addHandler(writeToFile, file=log_file_name, level='INFO')
  
  ##-----Load the Data-----
  con = dbConnect(SQLite(), dbname="Data/clean_basketball_data.db") #connect to sql database with all the data
  
  slots_2017 <- get_table_from_basketball("slots_2017")
  matchups_2017 <- get_table_from_basketball("matchups_2017")
  game_data_2017 <- get_table_from_basketball("game_data_2017")
  team_data_2017 <- get_table_from_basketball("team_data_2017")
  game_data_clean <- get_table_from_basketball("game_data_clean")
  team_data_clean <- get_table_from_basketball("team_data_clean") %>% select(-index)
  team_names <- get_table_from_basketball("team_names")
  seasons <- get_table_from_basketball("seasons")
  seeds <- get_table_from_basketball("seeds")
  slots <- get_table_from_basketball("slots")
  #season_results_compact <- get_table_from_basketball("season_results_compact")
  #season_results_detailed <- get_table_from_basketball("season_results_detailed")
  tourney_results_compact <- get_table_from_basketball("tourney_results_compact")
  tourney_results_complete <- get_table_from_basketball("tourney_results_complete")
  #tourney_results_detailed <- get_table_from_basketball("tourney_results_detailed")
  dbDisconnect(con) 
  
  
##########################################################################
##########   Section 2. Find the Best Model
##########################################################################
##-----Things that can be tweaked-----
# - Tourney data
# - Seasons included in the training
# - Variable being predicted
# - Game data
# - Weight of Home/Away
# - Last X number of games included in average



##-----Set up the data-----

## Just tourney results
win_indicators <- c(1,1,1) # this means return all "to predict" variables (score difference, 1/0 win/loss and 1/-1 win/loss)

#round1_results <- clean_tourney_results(tourney_results_compact,2012,win_indicators,1)



all_rounds_results <- clean_tourney_results(tourney_results_complete,2012,win_indicators,2)

#Create dataframe of any obs that have an NA / right now there are none!
contains_NA <- all_rounds_results[rowSums(is.na(all_rounds_results)) > 0,]


##-----Add Ken Pomeroy Season data-----
# Add team_data to all_rounds_results for future use
all_rounds_results <- add_more_data(all_rounds_results,team_data_clean,"SS_Year","WS_Year","SS_Team","WS_Team")

# Run all the models and add results to log
results_df <- run_all_models(all_rounds_results,"SS_Tm","WS_Tm","2016","Tourney results with Pomeroy season data")


##-----Add aggregated game-level data-----
loginfo("Adding aggregated game_level data. This section will try various combinations of a few things to see what gets the best results")
loginfo("There are two main things to be played with: 1. whether (and how much) away games are weighted relative to home games. and 2. how many of the most recent games to include in the averages")

## Add game data (no H/A weighting, all games)
game_data_agg_regseason <-  aggregate_game_data(game_data_clean,weight_away_diff=-1,take_last_X_games=-1) %>% select(-contains("Opp")) # - Only include the teams own stats, not opp too
results_df <- run_all_models(add_more_data(all_rounds_results,game_data_agg_regseason,"SS_Year","WS_Year","SS_Tm","WS_Tm"),
                             "SS_Tm","WS_Tm","2016","Adding game averages, no weighting, all games",results_df)

# Keep only a subset of the game average variables
game_data_agg_regseason_subset <- game_data_agg_regseason %>% mutate(Tm_AT=Tm_AST / Tm_TOV,Tm_3PFG=Tm_3PA/Tm_FGA) %>% 
  select(Year,Tm,Tm_FTA,Tm_FT_pct,Tm_3P_pct,Tm_ORB,Tm_AT,Tm_3PFG) %>% select(-contains("Opp"))
results_df <- run_all_models(add_more_data(all_rounds_results,game_data_agg_regseason_subset,"SS_Year","WS_Year","SS_Tm","WS_Tm"),
                             "SS_Tm","WS_Tm","2016","Adding game averages but keeping only a subset of the variables",results_df)

## Game data (5/6 H/A weighting, last 15 games) 
game_data_agg_regseason <- aggregate_game_data(game_data_clean,weight_away_diff=5/6,take_last_X_games=15) %>% select(-contains("Opp"))
results_df <- run_all_models(add_more_data(all_rounds_results,game_data_agg_regseason,"SS_Year","WS_Year","SS_Tm","WS_Tm"),
                             "SS_Tm","WS_Tm","2016","Weight away games as 5/6, include only last 15 games",results_df)

## Game data (2/3 weighting, all games) 
game_data_agg_regseason <-  aggregate_game_data(game_data_clean,weight_away_diff=2/3,take_last_X_games=-1) %>% select(-contains("Opp"))
results_df <- run_all_models(add_more_data(all_rounds_results,game_data_agg_regseason,"SS_Year","WS_Year","SS_Tm","WS_Tm"),
                             "SS_Tm","WS_Tm","2016","Weight away games as 2/3, include all games",results_df)

## away weighted as 3/4, all games included
game_data_agg_regseason <-  aggregate_game_data(game_data_clean,weight_away_diff=3/4,take_last_X_games=-1) %>% select(-contains("Opp"))
results_df <- run_all_models(add_more_data(all_rounds_results,game_data_agg_regseason,"SS_Year","WS_Year","SS_Tm","WS_Tm"),
                             "SS_Tm","WS_Tm","2016","Weight away games as 3/4, include all games",results_df)

## Try keeping only a subset of the game average variables
game_data_agg_regseason <-  aggregate_game_data(game_data_clean,weight_away_diff=19/20,take_last_X_games=11) %>% select(-contains("Opp"))
game_data_agg_regseason_subset <- game_data_agg_regseason %>% mutate(Tm_AT=Tm_AST / Tm_TOV,Tm_3PFG=Tm_3PA/Tm_FGA) %>% 
  select(Year,Tm,Tm_FTA,Tm_FT_pct,Tm_3P_pct,Tm_ORB,Tm_AT,Tm_3PFG)
results_df <- run_all_models(add_more_data(all_rounds_results,game_data_agg_regseason_subset,"SS_Year","WS_Year","SS_Tm","WS_Tm"),
                             "SS_Tm","WS_Tm","2016","Weight away games as 19/20, include las 11 games, subset of variables",results_df)

## 
game_data_agg_regseason_last10 <- aggregate_game_data(game_data_clean,weight_away_diff=3/4,take_last_X_games=10) %>% select(-contains("Opp"))
results_df <- run_all_models(add_more_data(all_rounds_results,game_data_agg_regseason_last10,"SS_Year","WS_Year","SS_Tm","WS_Tm"),
                             "SS_Tm","WS_Tm","2016","Weight away games as 3/4, include last 10 games",results_df)

## 
game_data_agg_regseason_last15 <- aggregate_game_data(game_data_clean,weight_away_diff=5/6,take_last_X_games=15) %>% select(-contains("Opp"))
#results_df <- run_all_models(add_more_data(all_rounds_results,game_data_agg_regseason_last15,"SS_Year","WS_Year","SS_Tm","WS_Tm"),
#               "SS_Tm","WS_Tm","2016","Weight away games as 5/6, include last 15 games",results_df)


###-----Summary of all Models-----
rownames(results_df) <- results_df[,1]
results_df[,1] <- NULL
results_df["Total" ,] <- colMeans(results_df)
results_df$RowMean <- rowMeans(results_df)
loginfo("I would go with 'Weight away games as 2/3, include all games' and SVM. That combination predicted 46 games correctly and appears to be more robust than other methods (meaning SVM consistently was in the top, and the average performance of all method was highest on that dataset.")

# Output a summary table. 
grid.newpage()
g <- tableGrob(results_df)
find_cell <- function(table, row, col, name="core-fg"){
  l <- table$layout
  which(l$t==row & l$l==col & l$name==name)
}

ind <- find_cell(g, 5, 4, "core-fg")
ind2 <- find_cell(g, 6, 8, "core-bg")
g$grobs[ind][[1]][["gp"]] <- gpar(fontsize=15, fontface="bold")
g$grobs[ind2][[1]][["gp"]] <- gpar(fill="darkolivegreen1", col = "darkolivegreen4", lwd=5)
grid.draw(g)
# This table shows a summary of the various data sets and models i tried.
#}  




##########################################################################
##########   Section 2. Predict Winners for 2017
##########################################################################

##-----Function to output submission-----
prepare_final_submission <- function(dataset,pred_var,outfilename){
  dataset$Id <- ifelse(dataset$SS_team < dataset$WS_team,paste0("2017_",dataset$SS_team,"_",dataset$WS_team),paste0("2017_",dataset$WS_team,"_",dataset$SS_team))
  dataset$Pred <- ifelse(dataset$SS_team < dataset$WS_team,dataset[,pred_var],1-dataset[,pred_var])
  for_submission <- dataset[,c("Id","Pred")]
  
  #mt. st marys beat new orleans
  for_submission$Pred[for_submission$Id == "2017_1291_1309"] <- 1.0
  #k state beat wake forest
  for_submission$Pred[for_submission$Id == "2017_1243_1448"] <- 1.0
  #nc central (1300) and uc davis
  for_submission$Pred[for_submission$Id == "2017_1300_1413"] <- 0.0
  #providence (1344) and usc
  for_submission$Pred[for_submission$Id == "2017_1344_1425"] <- 0.0
  
  write.csv(for_submission, file=paste0(outfilename,".csv"),row.names=FALSE)
  return(for_submission)
}




##-----Set up training data-----
model_training_data <- clean_tourney_results(tourney_results_complete,2012,c(1,1,1),2)
# add pomeroy season data
model_training_data <- add_more_data(model_training_data,team_data_clean,"SS_Year","WS_Year","SS_Team","WS_Team")
# add game averages
game_averages <-  aggregate_game_data(game_data_clean,weight_away_diff=2/3,take_last_X_games=-1) %>% select(-contains("Opp"))
model_training_data <- add_more_data(model_training_data,game_averages,"SS_Year","WS_Year","SS_Tm","WS_Tm")
model_training_data <- more_model_prep(model_training_data)
model_training_data$To_Predict <- model_training_data$SS_Win#_alt
model_training_data <- model_training_data %>% select(-Score_diff,-SS_Win,-SS_Win_alt,-WS_Name,-SS_Name,-Daynum,-Season,-WS_Conf,-SS_Conf)


##-----Set up "to predict" data-----
model_predict_data <- add_team_names(matchups_2017) %>% select(-index)
model_predict_data <- add_more_data(model_predict_data,team_data_2017,"SS_Year","WS_Year","SS_Team","WS_Team",for_final_model=TRUE) %>% select(-SS_index,-WS_index,-SS_Year,-WS_Year)

game_averages_2017 <-  aggregate_game_data(game_data_2017,weight_away_diff=2/3,take_last_X_games=-1) %>% select(-contains("Opp"))
model_predict_data <- add_more_data(model_predict_data,game_averages_2017,"SS_Year","WS_Year","SS_Tm","WS_Tm",for_final_model=TRUE) %>% select(-SS_Year,-WS_Year)
model_predict_data <- as.data.frame(unclass(model_predict_data))
model_predict_data <- model_predict_data[!duplicated(model_predict_data),]
model_predict_teams <- model_predict_data %>% select(WS_Name,SS_Name,WS_team,SS_team,SS_Seed,WS_Seed)
model_predict_data <- model_predict_data %>% select(-WS_Name,-SS_Name,-WS_team,-SS_team,-SS_Seed,-WS_Seed,-WS_Conf,-SS_Conf)




  

fit <- randomForest(as.factor(To_Predict) ~ ., data=model_training_data, importance=TRUE,ntree=1000) #ntree=2000

varImpPlot(fit) #look at what variables were important
plot(fit)
rf_pred <- predict(fit,model_predict_data,type="prob")
#
model_predict_teams$rforest_vals <- rf_pred[,1]
model_predict_teams$rforest_prob <- rf_pred[,2]

# prepares submission for kaggle contest
#tmp <- prepare_final_submission(model_predict_teams,"rforest_prob","RB_Submission_v2")


# files needed for running the simulations in python
write.csv(model_predict_teams,"Simulations/prediction_probabilities.csv",row.names=FALSE)
write.csv(slots_2017,"Simulations/slots_2017.csv",row.names=FALSE)



  
  
  ##-----Sources-----
  # Modeling
  # http://trevorstephens.com/kaggle-titanic-tutorial/r-part-5-random-forests/ 
  # http://nthturn.com/2015/02/22/prediction-using-random-forests-in-r-an-example/
  
  # Data
  # http://kenpom.com/
  # http://www.sports-reference.com/cbb/schools/air-force/2017.html : pulled this page for all schools, years 2012 to present
  # https://www.kaggle.com/c/march-machine-learning-mania-2017/data
  
  
  ##-----Ideas for future-----
  # - need to improve the actual modeling. SVM performed better than random forest, so should try to use that instead. Are there
  #   other methods that would have even better performance? like xgboost, naive bayes, ensemble methods, etc
  # - do some tests to see what distribution score differences follow
  # - Need to do more research on what features are most predictive of winning. Some ideas for more features:
    # - distance from hometown to game site
    # - flag for "deepest run in last 4 years"-- this would be 0 (no playoffs), 1 (lost in 1st), 2 (lost in 32), 3 (lost in 16), etc
    # - incorporating past performance against the specific team they are playing (SS_series_wins, SS_series_losses)
      # - could i add how they did against each other if they've already played that season? or one layer deeper, how they fared 
      #   against teams they both played? For example, if teams A & B both played C and A beat C but B lost to C, how to include that?
    # - school size
    # - bench points
    # - player level statistics (average minutes played, number of starting freshman, number of McD all americans, average height, age, etc)
    # - vegas betting lines before start of tournament
    # - train on more years of data to avoid overfitting to more recent years. Though it might make sense to somehow weight recent years more heavily
    #       the idea being that a team that is good this year was more likely to have been good last year.
    # - figure out how to include the team names in the model so can capture things like "teams like often have upsets" or teams that often choke, etc
    
  
  
  
