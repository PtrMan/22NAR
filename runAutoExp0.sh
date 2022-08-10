# half automated script to compute scores in environments for different runs

for i in {1..7}; do
    ~/.dotnet/dotnet run > log14062022Run${i}_Qwithout.txt &
    sleep 18
done

# wait till completion of all parallel jobs
wait

# process logs

for i in {1..7}; do
    cat log14062022Run${i}_Qwithout.txt | grep -F "ENV score.episodesAvg="
done

# remove logs for next batch
#rm ./log14*Q_without.txt

