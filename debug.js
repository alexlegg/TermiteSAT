$(function () {
    $("button.shrink").on("click", function (e) {
        $(this).parent(".trace").get(0).hide();
        console.log($(this).parent(".trace"));
    });
});
